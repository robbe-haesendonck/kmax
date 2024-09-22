import os
import re

from pymake import parser
import z3
import kmax.vcommon as CM

from kmax.datastructures import Results
from kmax.algorithm.kbuild import Kbuild, contains_unexpanded

import kmax.settings
mlog = CM.getLogger(__name__, kmax.settings.logger_level)

def isz3false(z):
    s = z3.Solver()
    s.add(z3.simplify(z))
    return z3.sat != s.check()

class Run:
    def __init__(self) -> None:
        self.results = Results()
        self.kbuild = Kbuild()
        print(f"Kbuild: {self.kbuild}")
    
    def run(self, makefiledirs):
        """
        Run the algorithm on the given makefiles.
        """
        assert isinstance(makefiledirs, (set, list)) \
            and makefiledirs, makefiledirs
        assert all(os.path.isfile(f) or os.path.isdir(f)
                   for f in makefiledirs), makefiledirs

        subdirs = set(makefiledirs)
        while subdirs:
            makefile = subdirs.pop()
            mlog.info(f"Processing makefile: {makefile}")            
            subdirs_ = self.extract(makefile)
            # # TODO: support recursive application of kmax when subdir-y is used, updating the current path, e.g., arch/arm64/boot/dts/amd/Makefile uses var from parent arch/arm64/boot/dts/Makefile
            # if kmax.settings.do_recursive:
            #     subdirs = subdirs.union(subdirs_)

    def extract(self, path):
        makefile = self.get_makefile(path)

        path = os.path.dirname(makefile)
        makefile = open(makefile, "r")

        s = makefile.read()
        makefile.close()

        self.kbuild.add_definitions(kmax.settings.defines)
        stmts = parser.parsestring(s, makefile.name)

        self.kbuild.process_stmts(stmts, self.kbuild.bdd.T, self.kbuild.zsolver.T)
        # SPECIAL-obj-simple uses a simply-expanded variable to expand obj-y in case obj-y is recursively-expanded, which means the variables haven't been expanded in obj-y yet, e.g., ptrace_$(BITS)
        self.kbuild.process_stmts(parser.parsestring("SPECIAL-obj-simple := $(obj-y) $(obj-m)", makefile.name), self.kbuild.bdd.T, self.kbuild.zsolver.T)
        self.kbuild.process_stmts(parser.parsestring("SPECIAL-lib-simple := $(lib-y) $(lib-m)", makefile.name), self.kbuild.bdd.T, self.kbuild.zsolver.T)
        self.kbuild.process_stmts(parser.parsestring("SPECIAL-core-simple := $(core-y) $(core-m) $(drivers-y) $(drivers-m) $(net-y) $(net-m) $(libs-y) $(libs-m) $(head-y) $(head-m)", makefile.name), self.kbuild.bdd.T, self.kbuild.zsolver.T)
        self.kbuild.process_stmts(parser.parsestring("SPECIAL-subdir-simple := $(subdir-y) $(subdir-m)", makefile.name), self.kbuild.bdd.T, self.kbuild.zsolver.T)

        presence_conditions = {}
        self.kbuild.get_presence_conditions([ "obj-y", "obj-m", "lib-y", "lib-m", "SPECIAL-obj-simple", "SPECIAL-lib-simple" ], presence_conditions, self.kbuild.bdd.T, self.kbuild.zsolver.T)
        self.results.presence_conditions = self.kbuild.deduplicate_and_add_path(presence_conditions, path)

        presence_conditions = {}
        self.kbuild.get_presence_conditions([ "core-y", "core-m",
                                         "drivers-y", "drivers-m", "net-y", "net-m", "libs-y",
                                         "libs-m", "head-y", "head-m", "SPECIAL-core-simple"], presence_conditions,
                                       self.kbuild.bdd.T, self.kbuild.zsolver.T)
        self.results.presence_conditions = self.kbuild.deduplicate_and_add_path(presence_conditions, "", self.results.presence_conditions)

        presence_conditions = {}
        self.kbuild.get_presence_conditions([ "subdir-y", "subdir-m", "SPECIAL-subdir-simple" ], presence_conditions, self.kbuild.bdd.T, self.kbuild.zsolver.T)
        subdirs_pcs = self.kbuild.deduplicate_and_add_path(presence_conditions, path)
        subdirs = list(subdirs_pcs.keys())

        subdirs_pcs_fixed = {}
        for subdir in list(subdirs_pcs.keys()):
            # add / to end of subdirs
            if not subdir.endswith("/"):
                fixed_subdir = subdir + "/"
            else:
                fixed_subdir = subdir
            subdirs_pcs_fixed[fixed_subdir] = subdirs_pcs[subdir]
        self.results.presence_conditions = self.kbuild.deduplicate_and_add_path(subdirs_pcs_fixed, "", self.results.presence_conditions)

        if kmax.settings.output_all_unit_types:
            self.results.units_by_type['subdirs'] = subdirs

            # mapping from unit type name to structure holding them
            self.results.units_by_type['compilation_units'] = list(self.results.presence_conditions.keys())

            self.kbuild.process_stmts(parser.parsestring("SPECIAL-extra := $(extra-y)", makefile.name), self.kbuild.bdd.T, self.kbuild.zsolver.T)
            presence_conditions = {}
            self.kbuild.get_presence_conditions([ "SPECIAL-extra", "extra-y" ], presence_conditions, self.kbuild.bdd.T, self.kbuild.zsolver.T)
            self.results.units_by_type['extra'] = list(self.kbuild.deduplicate_and_add_path(presence_conditions, path).keys())

            self.kbuild.process_stmts(parser.parsestring("SPECIAL-hostprogs := $(hostprogs-y) $(hostprogs-m) $(hostprogs) $(always)", makefile.name), self.kbuild.bdd.T, self.kbuild.zsolver.T)
            presence_conditions = {}
            self.kbuild.get_presence_conditions([ "SPECIAL-hostprogs", "hostprogs-y", "hostprogs-m", "hostprogs", "always" ], presence_conditions, self.kbuild.bdd.T, self.kbuild.zsolver.T)
            self.results.units_by_type['hostprog_units'] = list(self.kbuild.deduplicate_and_add_path(presence_conditions, path).keys())

            self.kbuild.process_stmts(parser.parsestring("SPECIAL-targets := $(targets)", makefile.name), self.kbuild.bdd.T, self.kbuild.zsolver.T)
            presence_conditions = {}
            self.kbuild.get_presence_conditions([ "SPECIAL-targets", "targets" ], presence_conditions, self.kbuild.bdd.T, self.kbuild.zsolver.T)
            self.results.units_by_type['targets'] = list(self.kbuild.deduplicate_and_add_path(presence_conditions, path).keys())

            self.kbuild.process_stmts(parser.parsestring("SPECIAL-clean-files := $(clean-files)", makefile.name), self.kbuild.bdd.T, self.kbuild.zsolver.T)
            presence_conditions = {}
            self.kbuild.get_presence_conditions([ "SPECIAL-clean-files", "clean-files" ], presence_conditions, self.kbuild.bdd.T, self.kbuild.zsolver.T)
            self.results.units_by_type['clean_files'] = list(self.kbuild.deduplicate_and_add_path(presence_conditions, path).keys())

            unconfigurable_prefixes = set([ "obj-$", "lib-$", "hostprogs-$" ])

            unconfigurable_variables = set([])
            for x in self.kbuild.variables:
                for p in unconfigurable_prefixes:
                    if x.startswith(p) and \
                            not x.endswith("-") and \
                            not x.endswith("-y") and \
                            not x.endswith("-m") and \
                            not x.endswith("-objs") and \
                            x != "hostprogs":
                        unconfigurable_variables.add(x)
                    elif x.startswith(p[:-1]) and x.endswith("-"):
                        # also look in variables resulting from expansion of
                        # undefined config var
                        unconfigurable_variables.add(x)

            presence_conditions = {}
            self.kbuild.get_presence_conditions(unconfigurable_variables, presence_conditions, self.kbuild.bdd.T, self.kbuild.zsolver.T)
            self.results.units_by_type['unconfigurable_units'] = list(self.kbuild.deduplicate_and_add_path(presence_conditions, path).keys())

        if kmax.settings.do_table:
            mlog.info(self.kbuild.getSymbTable(printCond=self.kbuild.bdd_to_str))        
        return subdirs

    @classmethod
    def get_makefile(cls, path):
        #use Kbuild file if found, otherwise try Makefile
        if os.path.isdir(path):
            makefile = os.path.join(path, "Kbuild")
            if not os.path.isfile(makefile):
                makefile = os.path.join(path, "Makefile")

                if not os.path.isfile(makefile):
                    mlog.error("{} not found".format(makefile))
                    exit(1)
        else:
            assert os.path.isfile(path), path
            makefile = path

        return makefile
    
    @classmethod
    def check_unexpanded_vars(cls, l, desc):
        for x in l:
            if contains_unexpanded(x):
                mlog.warn("A {} contains an unexpanded variable or call {}".format(desc, x))
