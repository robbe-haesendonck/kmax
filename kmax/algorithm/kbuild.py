import os
import re

from pymake import parser, parserdata, data, functions
from functools import reduce
import z3

import kmax.vcommon as CM

from kmax.datastructures import CondDef, Multiverse, VarEntry, BoolVar
from kmax import settings

from kmax.algorithm.kmax_bdd import KmaxBDD
from kmax.algorithm.zsolver import ZSolver

mlog = CM.getLogger(__name__, settings.logger_level)


def zconj(a, b): return None if a is None or b is None else z3.simplify(z3.And(a, b))
def zdisj(a, b): return None if a is None or b is None else z3.simplify(z3.Or(a, b))
def zneg(a): return None if a is None else z3.simplify(z3.Not(a))

def isBooleanConfig(name):
    return False

def isNonbooleanConfig(name):
    return False

match_unexpanded_variables = re.compile(r'.*\$\(.*\).*')

def contains_unexpanded(s):
    """
    return for strings such as $(test)
    """
    assert s is None or isinstance(s, str), s

    return s is not None and match_unexpanded_variables.match(s)

class Kbuild:
    def __init__(self):
        self.bdd = KmaxBDD()
        self.zsolver = ZSolver()

        self.variables = {}
        self.bvars = {}
        self.reverse_bvars = {}
        self.undefined_variables = set()
        self.var_equiv_sets = {}

    def process_stmts(self, stmts, cond, zcond):
        """Find configurations in the given list of stmts under the
        given presence cond."""
        for s in stmts:
            if isinstance(s, parserdata.ConditionBlock):
                self.process_conditionblock(s, cond, zcond)
            elif isinstance(s, parserdata.SetVariable):
                self.process_setvariable(s, cond, zcond)
            elif isinstance(s, (parserdata.Rule, parserdata.StaticPatternRule)):
                self.process_rule(s, cond, zcond)
            elif (isinstance(s, parserdata.Include)):
                self.process_include(s, cond, zcond)
            else:
                mlog.warn("cannot parse ({})".format(s))

    def get_bvars(self, name):
        """
        Mapping of boolean variable names to BDD variable number.
        Automatically increments the variable number.
        """
        
        assert isinstance(name, str), name
        try:
            return self.bvars[name]
        except KeyError:
            idx = len(self.bvars)
            bdd = self.bdd.bdd_ithvar(idx)
            zbdd = z3.Bool(name.format(idx))
            bv = BoolVar(bdd, zbdd, idx)
            self.bvars[name] = bv
            self.reverse_bvars[idx] = name
            return bv
    
    def get_var_equiv(self, name):
        """
        Get a new randomized variable name that is equivalent to the
        given variable.  this also updates a structure that records
        which variables are equivalent
        """

        assert isinstance(name, str), name

        if name in self.var_equiv_sets:
            name_ = "{}_EQUIV{}".format(len(self.var_equiv_sets[name]), name)
            self.var_equiv_sets[name].add(name_)
            return name_
        else:
            self.var_equiv_sets[name] = set([name])
            return name
        
    def get_var_equiv_set(self, name):
        if name not in self.var_equiv_sets:
            self.var_equiv_sets[name] = set([name])
            
        return self.var_equiv_sets[name]

    def getSymbTable(self, printCond=None):

        f = lambda vs: '\n'.join("{}. {}".format(i + 1, v.__str__(printCond))
                                 for i, v in enumerate(vs))

        ss = [(name, [v for v in self.variables[name] if v.val])
              for name in self.variables]
        ss = ["var: {}:\n{}\n---------".format(name, f(vs))
              for name, vs in ss if vs]

        return '\n'.join(ss)
    
    def get_presence_conditions(self, vars, pcs, cond, zcond, visited=set()):
        names = set()
        for var in vars:
            if var in list(self.variables.keys()):
                names = names.union(self.get_var_equiv_set(var))

        # ignore undefined vars
        names = [ name for name in names if name in list(self.variables.keys()) ]

        # prevent cycles, e.g., linux-3.19/net/mac80211/Makefile
        names = [ name for name in names if name not in visited ]
        for name in names: visited.add(name)
        
        while len(names) > 0:
            name = names.pop()
            for value, bdd_condition, z3_condition, flavor in self.variables[name]:
                tokens = value.split()
                for token in tokens:
                    and_cond = self.bdd.conj(cond, bdd_condition)
                    and_zcond = zconj(zcond, z3_condition)
                    if token not in list(pcs.keys()):
                        pcs[token] = and_zcond
                    else:
                        pcs[token] = zdisj(pcs[token], and_zcond)
                    if token.endswith(".o"): # and unit_name not in compilation_units:
                        if (token[:-2] + "-objs") in self.variables or \
                            (token[:-2] + "-y") in self.variables:
                            # scripts/Makefile.build use the -objs and -y
                            # suffix to define composites $($(subst
                            # $(obj)/,,$(@:.o=-objs))) $($(subst
                            # $(obj)/,,$(@:.o=-y)))), $^)
                            composite_variable1 = token[:-2] + "-objs"
                            composite_variable2 = token[:-2] + "-y"
                            # expand the variables for the composite unit, in case it has recursively-expanded variables, e.g., linux-3.19/fs/ramfs/Makefile
                            special_composite = "SPECIAL-composite-%s" % (token[:-2])
                            self.process_stmts(parser.parsestring("%s := $(%s) $(%s)" % (special_composite, composite_variable1, composite_variable2),
                                                                    "composite"),
                                                 and_cond, and_zcond)
                            self.get_presence_conditions([ special_composite, composite_variable1, composite_variable2 ], pcs, and_cond, and_zcond, visited)

    def deduplicate_and_add_path(self, presence_conditions, path=None, updated_presence_conditions = None):
        if updated_presence_conditions is None:
            updated_presence_conditions = {}
        for token in presence_conditions:
            # resolve any uses of ../ or ./
            filename = os.path.join(path, token)
            if filename not in list(updated_presence_conditions.keys()):
                updated_presence_conditions[filename] = presence_conditions[token]
            else:
                updated_presence_conditions[filename] = zdisj(updated_presence_conditions[filename], presence_conditions[token])
        return updated_presence_conditions

    def add_definitions(self, defines):
        if not defines:
            return
        
        for define in defines:
            name, value = define.split("=")
            self.add_var(name, self.bdd.bdd_one(), self.zsolver.T, '=', value)

    def get_defined(self, variable, expected):
        # variable_name = "defined(" + variable + ")"
        # todo implement for tristate flag also, i.e., =y or =m and !=n
        variable_name = variable
        bdd = self.get_bvars(variable_name).bdd
        zbdd = self.get_bvars(variable_name).zbdd
        
        if expected:
            return bdd, zbdd
        else:
            return self.bdd.neg(bdd), z3.Not(zbdd)

    def process_variableref(self, name):
        # linux-specific non-Booleans
        if name not in self.variables and name == 'BITS':
            # TODO get real entry from top-level makefiles
            bv32 = self.get_bvars("BITS=32")
            bv64 = self.get_bvars("BITS=64")
            return Multiverse(
                self.bdd,
                [
                    CondDef(bv32.bdd, bv32.zbdd, "32"),
                    CondDef(bv64.bdd, bv64.zbdd, "64")
                ]
            )
        elif name == "CONFIG_WORD_SIZE":
            # TODO get defaults from Kconfig files
            bv32 = self.get_bvars("CONFIG_WORD_SIZE=32")
            bv64 = self.get_bvars("CONFIG_WORD_SIZE=64")
            return Multiverse(self.bdd, [ CondDef(bv32.bdd, bv32.zbdd, "32"),
                                CondDef(bv64.bdd, bv64.zbdd, "64") ])
        elif name not in self.variables and (name == "MMU" or name == "MMUEXT"):
            # TODO get globals from arch Makefiles
            is_defined, zis_defined = self.get_defined("CONFIG_MMU", True)
            not_defined, znot_defined = self.get_defined("CONFIG_MMU", False)

            return Multiverse(self.bdd, [ CondDef(is_defined, zis_defined, ''),
                                CondDef(not_defined, znot_defined, '-nommu') ])
        elif name.startswith("CONFIG_"):
            if settings.do_boolean_configs:
                #varbdd = self.bvars[name].bdd
                v = self.get_bvars(name).bdd
                zv = self.get_bvars(name).zbdd

                # if a list of free options was given on the
                # command-line, then only allow those options to be
                # free variables, otherwise the configuration option
                # is always disabled.
                if settings.unselectable != None and name in settings.unselectable:
                    return Multiverse(self.bdd, [ CondDef(self.bdd.bdd_one(), self.zsolver.T, None) ])
                else:
                    return Multiverse(self.bdd, [ CondDef(v, zv, 'y'),
                                        CondDef(self.bdd.neg(v), z3.Not(zv), None) ])
            else:
                # TODO don't use 'm' for truly boolean config vars
                equals_y = self.get_bvars(name + "=y").bdd
                zequals_y = self.get_bvars(name + "=y").zbdd

                equals_m = self.get_bvars(name + "=m").bdd
                zequals_m = self.get_bvars(name + "=m").zbdd

                defined, zdefined = self.get_defined(name, True)
                is_defined_y = self.bdd.conj(defined, self.bdd.conj(equals_y, self.bdd.neg(equals_m)))
                zis_defined_y = zconj(zdefined, zconj(zequals_y, z3.Not(zequals_m)))


                is_defined_m = self.bdd.conj(defined, self.bdd.conj(equals_m, self.bdd.neg(equals_y)))
                zis_defined_m = zconj(zdefined, zconj(zequals_m, z3.Not(zequals_y)))

                notdefined, znotdefined = self.get_defined(name, False)
                not_defined = self.bdd.disj(notdefined, self.bdd.conj(self.bdd.neg(is_defined_y), self.bdd.neg(is_defined_m)))
                znot_defined = zdisj(znotdefined, zconj(z3.Not(zis_defined_y), z3.Not(zis_defined_m)))   


                return Multiverse(self.bdd, [ CondDef(is_defined_y, zis_defined_y, 'y'),
                                    CondDef(is_defined_m, zis_defined_m, 'm'),
                                    CondDef(not_defined, znot_defined, None) ])
        # elif (name.startswith("CONFIG_")) and not isNonbooleanConfig(name):
        #     return Multiverse([ (self.bdd.bdd_one(), '') ])
        else:
            if name in self.undefined_variables:
                return Multiverse(self.bdd, [v.condDef for v in self.variables[name]])
            
            elif name not in self.variables and not isNonbooleanConfig(name):
                # Leave undefined variables unexpanded
                self.undefined_variables.add(name)
                self.variables[name] = [VarEntry("$(%s)" % (name),
                                                 self.bdd.bdd_one(), self.zsolver.T,
                                                 VarEntry.RECURSIVE)]

                mlog.warn("Undefined variable expansion: {}".format(name))
                return Multiverse(self.bdd, [v.condDef for v in self.variables[name]])
            
            else:
                expansions = []
                equivs = self.get_var_equiv_set(name)
                for equiv_name in equivs:
                    for v in self.variables[equiv_name]:
                        if v.val:
                            expansions = expansions + self.expand_and_flatten(v.val, v.cond, v.zcond)
                        else:
                            expansions.append(v.condDef)

                return Multiverse(self.bdd, expansions)

    def process_function(self, function):
        """Evaluate variable expansion or built-in function and return
        either a single string or a list of (condition, string) pairs."""
        if isinstance(function, functions.VariableRef):
            return self.process_fun_VariableRef(function)
        elif isinstance(function, functions.SubstFunction):
            return self.process_fun_SubstFunction(function)
        elif isinstance(function, functions.SubstitutionRef):
            return self.process_fun_SubstitutionRef(function)
        elif isinstance(function, functions.IfFunction):
            return self.process_fun_IfFunction(function)
        elif isinstance(function, functions.FilteroutFunction):
            return self.process_fun_FilteroutFunction(function)
        elif isinstance(function, functions.PatSubstFunction):
            return self.process_fun_PatSubstFunction(function)
        elif isinstance(function, functions.SortFunction):
            return Multiverse(self.bdd, self.mk_Multiverse(self.process_expansion(function._arguments[0])))
        elif isinstance(function, functions.AddPrefixFunction):
            return self.process_fun_AddPrefixFunction(function)
        elif isinstance(function, functions.AddSuffixFunction):
            return self.process_fun_AddSuffixFunction(function)
        elif isinstance(function, functions.ShellFunction):
            return self.process_fun_ShellFunction(function)
        else:
            mlog.warn("default on function: {}".format(function))
            return self.mk_Multiverse(function.to_source())

    def process_fun_VariableRef(self, function):
        name = self.mk_Multiverse(self.process_expansion(function.vname))
        expanded_names = []
        for name_cond, name_zcond, name_value  in name:
            expanded_name = self.process_variableref(name_value)
            assert isinstance(expanded_name, Multiverse), expanded_name

            for v in expanded_name:
                expanded_names.append(
                    CondDef(self.bdd.conj(name_cond, v.cond), zconj(name_zcond, v.zcond), v.mdef)
                )
        return Multiverse(self.bdd, expanded_names)

    def process_fun_SubstFunction(self, function):
        from_vals = self.mk_Multiverse(self.process_expansion(function._arguments[0]))
        to_vals = self.mk_Multiverse(self.process_expansion(function._arguments[1]))
        in_vals = self.mk_Multiverse(self.process_expansion(function._arguments[2]))

        # Hoist conditionals around the function by getting all
        # combinations of arguments
        hoisted_results = []
        for (sc, szc, s), (rc, rzc, r), (dc, dzc, d) in zip(from_vals, to_vals, in_vals):
            instance_cond = self.bdd.conj(sc, self.bdd.conj(rc, dc))
            instance_zcond = z3.simplify(z3.And(szc, rzc, dzc))
            if not self.bdd.isfalse(instance_cond, instance_zcond):
                if r is None: r = ""  # Fixes bug in net/l2tp/Makefile
                instance_result = None if d is None else d.replace(s, r)
                hoisted_results.append(CondDef(instance_cond, instance_zcond, instance_result))

        return Multiverse(self.bdd, hoisted_results)
        
    def process_fun_IfFunction(self, function):
        cond_part = self.mk_Multiverse(self.process_expansion(function._arguments[0]))
        then_part = self.mk_Multiverse(self.process_expansion(function._arguments[1]))
        then_cond = self.bdd.bdd_zero()
        then_zcond = self.zsolver.F
        else_cond = self.bdd.bdd_zero()
        else_zcond = self.zsolver.F
        for cond, zcond, value in cond_part:
            if value:
                then_cond = self.bdd.disj(then_cond, cond)
                then_zcond = zdisj(then_zcond, zcond)
            else:
                else_cond = self.bdd.disj(then_cond, cond)
                else_zcond = zdisj(then_zcond, zcond)

        expansions = []

        for cond, zcond, value in then_part:
            cond = self.bdd.conj(then_cond, cond)
            zcond = zconj(then_zcond, zcond)
            if not self.bdd.isfalse(cond, zcond):
                expansions.append(CondDef(cond, zcond, value))

        if len(function._arguments) > 2:
            else_part = self.mk_Multiverse(self.process_expansion(function._arguments[2]))
            for cond, zcond, value in else_part:
                cond = self.bdd.conj(else_cond, cond)
                zcond = zconj(else_zcond, zcond)

                if not self.bdd.isfalse(cond, zcond):
                    expansions.append(CondDef(cond, zcond, value))

        return Multiverse(self.bdd, expansions)

    def process_fun_FilteroutFunction(self, function):
        from_vals = self.mk_Multiverse(self.process_expansion(function._arguments[0]))
        in_vals = self.mk_Multiverse(self.process_expansion(function._arguments[1]))

        # Hoist conditionals around the function by getting all
        # combinations of arguments
        hoisted_args = tuple((s, d) for s in from_vals for d in in_vals)
        hoisted_results = []
        # Compute the function for each combination of arguments
        for (c1, zc1, s), (c2, zc2, d) in hoisted_args:
            instance_cond = self.bdd.conj(c1, c2)
            instance_zcond = zconj(zc1, zc2)

            if not self.bdd.isfalse(instance_cond, instance_zcond):
                if d is None:
                    instance_result = None
                else:
                    instance_result = " ".join(d_token for d_token in d.split() if d_token != s)

                cd = CondDef(instance_cond, instance_zcond, instance_result)
                hoisted_results.append(cd)

        return Multiverse(self.bdd, hoisted_results)

    def process_fun_PatSubstFunction(self, function):
        from_vals = self.mk_Multiverse(self.process_expansion(function._arguments[0]))
        to_vals = self.mk_Multiverse(self.process_expansion(function._arguments[1]))
        in_vals = self.mk_Multiverse(self.process_expansion(function._arguments[2]))

        # Hoist conditionals around the function by getting all
        # combinations of arguments
        hoisted_args = tuple((s, r, d)
                             for s in from_vals
                             for r in to_vals
                             for d in in_vals)
        hoisted_results = []
        # Compute the function for each combination of arguments
        for (c1, zc1, s), (c2, zc2, r), (c3, zc3, d) in hoisted_args:
            instance_cond = self.bdd.conj(c1, self.bdd.conj(c2, c3))
            instance_zcond = z3.simplify(z3.And(zc1, zc2, zc3))
            
            if not self.bdd.isfalse(instance_cond, instance_zcond):
                if r == None: r = ""  # Fixes bug in net/l2tp/Makefile
                pattern = "^" + s.replace(r"%", r"(.*)", 1) + "$"
                replacement = r.replace(r"%", r"\1", 1)
                if d is None:
                    instance_result = None
                else:
                    instance_result = " ".join(re.sub(pattern, replacement, d_token)
                                               for d_token in d.split())
                cd = CondDef(instance_cond, instance_zcond, instance_result)
                hoisted_results.append(cd)
                
        return Multiverse(self.bdd, hoisted_results)

    def process_fun_AddPrefixFunction(self, function):
        prefixes = self.mk_Multiverse(self.process_expansion(function._arguments[0]))
        token_strings = self.mk_Multiverse(self.process_expansion(function._arguments[1]))

        hoisted_results = []
        for (prefix_cond, prefix_zcond, prefix) in prefixes:
            for (tokens_cond, tokens_zcond, token_string) in token_strings:
                resulting_cond = self.bdd.conj(prefix_cond, tokens_cond)
                resulting_zcond = zconj(prefix_zcond, tokens_zcond)

                if not self.bdd.isfalse(resulting_cond, resulting_zcond):
                    # append prefix to each token in the token_string
                    if token_string is None:
                        prefixed_tokens = ""                            
                    else:
                        prefixed_tokens = " ".join(prefix + token
                                                   for token in token_string.split())
                    hoisted_results.append(CondDef(resulting_cond, resulting_zcond, prefixed_tokens))

        # sys.stderr.write("prefix: %s\n" % (str(hoisted_results)))
        return Multiverse(self.bdd, hoisted_results)
        
    def process_fun_AddSuffixFunction(self, function):
        suffixes = self.mk_Multiverse(self.process_expansion(function._arguments[0]))
        token_strings = self.mk_Multiverse(self.process_expansion(function._arguments[1]))

        hoisted_results = []
        for (suffix_cond, suffix_zcond, suffix) in suffixes:
            for (tokens_cond, tokens_zcond, token_string) in token_strings:
                resulting_cond = self.bdd.conj(suffix_cond, tokens_cond)
                resulting_zcond = zconj(suffix_zcond, tokens_zcond)

                if not self.bdd.isfalse(resulting_cond, resulting_zcond):
                    # append suffix to each token in the token_string
                    if token_string is None:
                        suffixed_tokens = ""                            
                    else:
                        suffixed_tokens = " ".join(token + suffix
                                                   for token in token_string.split())
                    hoisted_results.append(CondDef(resulting_cond, resulting_zcond, suffixed_tokens))

        # sys.stderr.write("suffix: %s\n" % (str(hoisted_results)))
        return Multiverse(self.bdd, hoisted_results)
        
    def process_fun_SubstitutionRef(self, function):
        from_values = self.mk_Multiverse(self.process_expansion(function.substfrom))
        to_values = self.mk_Multiverse(self.process_expansion(function.substto))
        name = self.mk_Multiverse(self.process_expansion(function.vname))

        # first expand the variable
        in_values = []
        for name_cond, name_zcond, name_value in name:
            expanded_name = self.process_variableref(name_value)
            for (expanded_cond, expanded_zcond, expanded_value) in expanded_name:
                resulting_cond = self.bdd.conj(name_cond, expanded_cond)
                resulting_zcond = zconj(name_zcond, expanded_zcond)
                in_values.append( (resulting_cond, resulting_zcond, expanded_value) )

        # then do patsubst
        hoisted_arguments = tuple((s, r, d)
                                  for s in from_values
                                  for r in to_values
                                  for d in in_values)

        hoisted_results = []
        for (c1, zcond1, s), (c2, zcond2, r), (c3, zcond3, d) in hoisted_arguments:
            instance_condition = self.bdd.conj(c1, self.bdd.conj(c2, c3))
            instance_zcondition = zconj(zcond1, zconj(zcond2, zcond3))
            if instance_condition != self.bdd.bdd_zero():
                if r == None: r = ""  # Fixes bug in net/l2tp/Makefile
                if r"%" not in s:
                    # without a %, use a % to implement replacing
                    # the end of the string
                    s = r"%" + s
                    r = r"%" + r
                pattern = "^" + s.replace(r"%", r"(.*)", 1) + "$"
                replacement = r.replace(r"%", r"\1", 1)
                if d is None:
                    instance_result = None
                else:
                    instance_result = " ".join([re.sub(pattern, replacement, d_token) for d_token in d.split()])
                hoisted_results.append((instance_condition, instance_zcondition, instance_result))

        return Multiverse(self.bdd, hoisted_results)

    def process_fun_ShellFunction(self, function):
        unexpanded_arg = function._arguments[0]
        # expanded_args = self.mk_Multiverse(self.process_expansion(arg))
        # for arg_cond, arg_zcond, arg_value in expanded_args:
        #     pass
        if unexpanded_arg == unexpanded_arg:
            mlog.info("assuming $(shell uname -a) expands to Linux")
            return self.mk_Multiverse("Linux")
        else:
            mlog.warn("shell calls are not supported: {}".format(function))
            return self.mk_Multiverse(function.to_source())
        
    def mk_Multiverse(self, expansion):
        assert isinstance(expansion, (str, Multiverse)), expansion
        
        if isinstance(expansion, str):
            return Multiverse(self.bdd, [CondDef(self.bdd.bdd_one(), self.zsolver.T, expansion)])
        else:
            return expansion

    def process_element(self, element, isfunc):
        if isinstance(element, str):
            return element
        elif isfunc:
            ret = self.process_function(element)
            return ret
        else:
            ret = self.process_expansion(element)
            return ret

    def hoist(self, expansion):
        """Hoists a list of expansions, strings, and Multiverses.
        return a Multiverse
        """
        #trace()
        hoisted = [(self.bdd.T, self.zsolver.T, [])]
        for element in expansion:
            if isinstance(element, Multiverse):
                newlist = []
                for subcondition, zsubcondition, subverse in element:
                    for condition, zcondition, verse in hoisted:
                        newcondition = self.bdd.conj(condition, subcondition)
                        newzcondition = zconj(zcondition, zsubcondition)

                        # filter infeasible combinations
                        if not self.bdd.isfalse(newcondition, newzcondition):
                            newverse = list(verse)
                            if isinstance(subverse, list):
                                newverse += subverse
                            else:
                                newverse.append(subverse)
                            newlist.append((newcondition, newzcondition, newverse))
                hoisted = newlist
            else:
                for condition, zcondition, verse in hoisted:
                    verse.append(element)

        multiverse = Multiverse(self.bdd, [CondDef(condition, zcondition, self.join_values(verse))
                                 for condition, zcondition, verse in hoisted] )

        multiverse = multiverse.dedup()
        return multiverse

    def process_expansion(self, expansion):
        """Expand variables in expansion, hoisting multiply-defined ones

        @param expansion is a pymake Expansion object

        @return either a single string or a Multiverse, i.e., list of (condition, string)
        pairs."""

        # sys.stderr.write("process_expansion: %s\n" % (str(expansion)))
        if isinstance(expansion, data.StringExpansion):
            return expansion.s
        elif isinstance(expansion, data.Expansion):
            rs = [
                self.process_element(element, isfunc)
                for element, isfunc in expansion
            ]
            mv = self.hoist(rs)
            assert isinstance(mv, Multiverse), mv
            # sys.stderr.write("process_expansion_Expansion: %s\n" % (str(mv)))
            return mv
        else:
            mlog.error("Unsupported BaseExpansion subtype: {}".format(expansion))
            exit(1)

    def process_conditionblock(self, block, presence_cond, presence_zcond):
        """Find a satisfying configuration for each branch of the
        conditional block."""
        # See if the block has an else branch.  Assumes no "else if".
        if len(block) == 1:
            has_else = False
        elif len(block) == 2:
            has_else = True
        else:
            mlog.warn("unsupported conditional block: {}".format(block))
            return

        # Process first branch
        cond, stmts = block[0]  # condition is a Condition object
        
        first_branch_cond = None
        first_branch_zcond = None
        
        if isinstance(cond, parserdata.IfdefCondition):  # ifdef
            # TODO only care if condition.exp.variable_references contains
            # multiply-defined macros
            expansion = self.process_expansion(cond.exp)
            if isinstance(expansion, str):
                first_branch_cond, first_branch_zcond = self.get_defined(expansion, cond.expected)
            else:
                #trace()
                cds = [cd for cd in expansion if cd.mdef is not None]
                hoisted_cond = reduce(self.bdd.disj, [cd.cond for cd in cds])
                hoisted_zcond = z3.simplify(z3.Or([cd.zcond for cd in cds]))

                first_branch_cond = hoisted_cond
                first_branch_zcond = hoisted_zcond

            first_branch_cond = self.bdd.conj(presence_cond, first_branch_cond)
            first_branch_zcond = zconj(presence_zcond, first_branch_zcond)

            else_branch_cond = self.bdd.neg(first_branch_cond)
            else_branch_zcond = z3.Not(first_branch_zcond)

        elif isinstance(cond, parserdata.EqCondition):  # ifeq
            exp1 = self.mk_Multiverse(
                self.process_expansion(cond.exp1)
            )
            exp2 = self.mk_Multiverse(
                self.process_expansion(cond.exp2)
            )

            # Hoist multiple expansions around equality operation
            hoisted_cond = self.bdd.F
            hoisted_zcond = self.zsolver.F
            
            hoisted_else = self.bdd.F
            hoisted_zelse = self.zsolver.F
            for cd1 in exp1:
                v1 = cd1.mdef if cd1.mdef else ""                
                for cd2 in exp2:
                    v2 = cd2.mdef if cd2.mdef else ""
                    term_cond = self.bdd.conj(cd1.cond, cd2.cond)
                    term_zcond = zconj(cd1.zcond, cd2.zcond)

                    #TODO: check term_zcond == term_cond
                    
                    if not self.bdd.isfalse(term_cond, term_zcond) and (v1 == v2) == cond.expected:
                        hoisted_cond = self.bdd.disj(hoisted_cond, term_cond)
                        hoisted_zcond = zdisj(hoisted_zcond, term_zcond)
                        
                    elif not self.bdd.isfalse(term_cond, term_zcond):
                        hoisted_else = self.bdd.disj(hoisted_else, term_cond)
                        hoisted_zelse = zdisj(hoisted_zelse, term_zcond)
                        
                    if contains_unexpanded(v1) or contains_unexpanded(v2):
                        # this preserves configurations where we
                        # didn't have values for a config option
                        v = self.get_bvars("{}={}".format(v1, v2))
                        bdd = v.bdd
                        zbdd = v.zbdd
                        hoisted_cond = self.bdd.disj(hoisted_cond, bdd)
                        hoisted_zcond = zdisj(hoisted_zcond, zbdd)
                        
                        hoisted_else = self.bdd.disj(hoisted_else, self.bdd.neg(bdd))
                        hoisted_zelse = zdisj(hoisted_zelse, z3.Not(zbdd))

                first_branch_cond = self.bdd.conj(presence_cond, hoisted_cond)
                first_branch_zcond = zconj(presence_zcond, hoisted_zcond)
                else_branch_cond = self.bdd.conj(presence_cond, hoisted_else)
                else_branch_zcond = zconj(presence_zcond, hoisted_zelse)
                
        else:
            mlog.error("unsupported conditional branch: {}".format(cond))
            exit(1)
        
        assert first_branch_zcond is not None, \
            "Could not get if branch cond {}".format(first_branch_zcond)
        
        # Enter first branch
        # trace()
        self.process_stmts(stmts, first_branch_cond, first_branch_zcond)

        if not has_else:
            return

        # Process the else branch
        cond, stmts = block[1]
        self.process_stmts(stmts, else_branch_cond, else_branch_zcond)  # Enter else branch

    def expand_and_flatten(self, val, cond, zcond):
        """Parse and expand a variable definition, flattening any
        recursive expansions by hoisting

        @return a Multiverse list of (cond, val) pairs"""
        # Parse the variable's definition
        d = parser.Data.fromstring(val, None)
        e, t, o = parser.parsemakesyntax(d, 0, (), parser.iterdata)
        if t != None or o != None:
            # TODO: do something if part of the string is left over
            pass

        expanded = self.process_expansion(e)
        if isinstance(expanded, str):
            return Multiverse(self.bdd, [CondDef(cond, zcond, expanded)])
        else: # must be a multiverse
            return expanded

    def join_values(self, value_list, delim=""):
        """Joins a list of make variable values that may be None, which
        means the variable is undefined.  When joined with defined values,
        None is the empty string.  When all values are None, the resulting
        value is also None.

        @param value_list a list of strings or Nones
        @returns A string or a None"""
        return delim.join(v for v in value_list if v)
    
    def append_values(self, *args):
        return self.join_values(args, " ")

    def bdd_to_dnf(self, condition):
        """Converts the expression to conjunctive normal form

        @returns a list of terms, represented as lists of factors"""

        solutions = self.bdd.bdd_solutions(condition)
        expression = []
        for solution_term in solutions:
            term = []
            for factor in solution_term:
                if solution_term[factor]:
                    term.append(self.reverse_bvars[factor])
                else:
                    term.append("!%s" % (self.reverse_bvars[factor]))
            expression.append(term)
        return expression

    def bdd_to_str(self, condition):
        """Converts the expression to a string"""

        expression = ""
        term_delim = ""
        for sublist in self.bdd_to_dnf(condition):
            term = ""
            factor_delim = ""
            for factor in sublist:
                term += factor_delim + factor
                factor_delim = " && "
            if len(term) > 0:
                expression += term_delim + term
                term_delim = " || "
        if len(expression) == 0:
            expression="1"
        return expression
    
    def update_vars(self, name, presence_cond, presence_zcond):
        var_entries = []
        
        for old_value_old_cond_old_zcond_old_flavor in self.variables[name]:
            var_entry = VarEntry(
                old_value_old_cond_old_zcond_old_flavor[0],
                self.bdd.conj(
                    old_value_old_cond_old_zcond_old_flavor[1],
                    self.bdd.neg(presence_cond)
                ),
                zconj(
                    old_value_old_cond_old_zcond_old_flavor[2],
                    z3.Not(presence_zcond)
                ),
                old_value_old_cond_old_zcond_old_flavor[3]
            )
            var_entries.append(var_entry)
        
        return var_entries




    def add_var(self, name, presence_cond, presence_zcond, token, value):
        """Given a presence cond, the variable's name, its assignment
        operator, and the definition, update the variable's list of
        configurations to reflect the dry-runs needed to cover all its
        definition."""

        assert value is not None, value

        if token == "=":
            # Recursively-expanded variable defs are expanded at use-time

            if not self.bdd.isfalse(presence_cond, presence_zcond):
                equivs = self.get_var_equiv_set(name)
                for equiv_name in equivs:
                    # Update all existing definitions' presence conds
                    if equiv_name in self.variables:
                        self.variables[equiv_name] = self.update_vars(equiv_name, presence_cond, presence_zcond)
                    else:
                        self.variables[equiv_name] = []

                    # Add complete definition to variable (needed to find variable
                    # expansions at use-time)
                    self.variables[equiv_name].append(
                        VarEntry(value, presence_cond, presence_zcond, VarEntry.RECURSIVE))
            else:
                mlog.warn("no feasible entries to add for {} {} {}".format(name, token, value))

        elif token == ":=":
            # Simply-expanded self.variables are expanded at define-time

            equivs = self.get_var_equiv_set(name)
            for equiv_name in equivs:
                # Update all existing definitions' presence conds
                # AFTER getting the new definition, since the new
                # definition might refer to itself as in
                # linux-3.0.0/crypto/Makefile

                if equiv_name in self.variables:
                    old_variables = self.update_vars(equiv_name, presence_cond, presence_zcond)
                else:
                    old_variables= [VarEntry("", 
                        self.bdd.neg(presence_cond), 
                        z3.Not(presence_zcond), 
                        VarEntry.RECURSIVE)]
                    # old_variables = []

                # Expand and flatten self.variables in the definition and add the
                # resulting definitions.
                new_definitions = self.expand_and_flatten(value, presence_cond, presence_zcond)

                new_variables = []
                for new_cond, new_zcond, new_value in new_definitions:
                    if not self.bdd.isfalse(new_cond, new_zcond):
                        new_variables.append(VarEntry(new_value, 
                                                        new_cond,
                                                        new_zcond,
                                                        VarEntry.SIMPLE))

                if len(old_variables + new_variables) > 0:
                    self.variables[equiv_name] = old_variables + new_variables
                else:
                    mlog.warn("no feasible entries to add for {} {} {}".format(name, token, value))
                # TODO: check for computed variable names, compute them, and
                # collect any configurations resulting from those self.variables

        elif token == "+=":
            # optimize append for certain variables this
            # optimization creates a new variable entry for
            # append instead of computing the cartesian
            # product of appended variable definitions
            simply = self.bdd.bdd_zero()
            zsimply = self.zsolver.F
            recursively = self.bdd.bdd_zero()
            zrecursively = self.zsolver.F

            new_var_name = self.get_var_equiv(name)

            # find conds for recursively- and simply-expanded variables
            if name in self.variables:
                for entry in self.variables[name]:
                    _, old_cond, old_zcond, old_flavor = entry
                    # TODO: optimization, memoize these
                    if old_flavor == VarEntry.SIMPLE:
                        simply = self.bdd.disj(simply, old_cond)
                        zsimply = zdisj(zsimply, old_zcond)
                    else:
                        assert old_flavor == VarEntry.RECURSIVE
                        recursively = self.bdd.disj(recursively, old_cond)
                        zrecursively = zdisj(zrecursively, old_zcond)

                if not self.bdd.isfalse(recursively, zrecursively):
                    if new_var_name not in self.variables:
                        self.variables[new_var_name] = []
                    self.variables[new_var_name].append(
                        VarEntry(value,
                                presence_cond,
                                presence_zcond,
                                VarEntry.RECURSIVE))

                if not self.bdd.isfalse(simply, zsimply):
                    new_definitions = self.expand_and_flatten(value, presence_cond,presence_zcond)
                    new_variables = []
                    for new_cond, new_zcond, new_value in new_definitions:
                        and_cond = self.bdd.conj(new_cond, presence_cond)
                        and_zcond = zconj(new_zcond, presence_zcond)
                        if not self.bdd.isfalse(and_cond, and_zcond):
                            new_variables.append(VarEntry(
                                new_value, and_cond, and_zcond, VarEntry.SIMPLE))

                    self.variables[new_var_name] = new_variables
                    # print("simply_done", new_variables)


            else:
                if not self.bdd.isfalse(presence_cond, presence_zcond):
                    self.variables[new_var_name] = [VarEntry(
                        value, presence_cond, presence_zcond, VarEntry.RECURSIVE)]
                else:
                    mlog.warn("no feasible entries to add for {} {} {}".format(name, token, value))
                
                    
        elif token == "?=":
            # TODO: if ?= is used on an undefined variable, it's
            # initialized as a recursively-expanded variable (=)

            pass
        
        else:
            mlog.error("Unknown setvariable token: {}".format(token))

        # Trim definitions with a presence cond of FALSE                    
        for equiv in self.get_var_equiv_set(name):
            if equiv in self.variables:
                self.variables[equiv] = \
                    [v for v in self.variables[equiv] if not self.bdd.isfalse(v.cond, v.zcond)]
                

    def process_setvariable(self, setvar, cond, zcond):
        """Find a satisfying set of configurations for variable."""
        # assert isinstance(cond, pycudd.DdNode), cond
        assert isinstance(setvar, parserdata.SetVariable), setvar
        assert z3.is_expr(zcond), zcond

        # obj-y = 'fork.o'
        name = self.process_expansion(setvar.vnameexp)
        token = setvar.token
        value = setvar.value

        if isinstance(name, str):
            # f(name, cond, zcond)  # remove because this method for presence conditions is obsolete
            self.add_var(name, cond, zcond, token, value)
        else:
            for local_cond, local_zcond, expanded_name in name:
                nested_cond = self.bdd.conj(local_cond, cond)
                nested_zcond = zconj(local_zcond, zcond)
                # f(expanded_name, nested_cond, nested_zcond)  # remove because this method for presence conditions is obsolete
                self.add_var(expanded_name, nested_cond, nested_zcond, token, value)

    def process_rule(self, rule, cond, zcond):
        # mlog.warn("just pass on rule {} {} {}".format(rule, self.bdd_to_str(cond), zcond))
        mlog.warn("just pass on rule {}".format(rule))
        pass

    def process_include(self, s, cond, zcond):
        expanded_include = self.mk_Multiverse(self.process_expansion(s.exp))
        for include_cond, include_zcond, include_files in expanded_include:
            if include_files != None:
                for include_file in include_files.split():
                    obj = os.path.dirname(include_file)
                    if os.path.exists(include_file):
                        include_makefile = open(include_file, "r")
                        s = include_makefile.read()
                        include_makefile.close()
                        include_stmts = parser.parsestring(s, include_makefile.name)
                        self.process_stmts(include_stmts, include_cond, include_zcond)

    def split_defs(self, var):
        """get every whitespace-delimited token in all definitions of the
        given var name, expanding any var invocations first"""

        if var not in self.variables:
            return []

        values = []
        for (value, cond, zcond, _) in self.variables[var]:
            assert value is not None, value
            # Expand any vars used in definitions

            expanded_values = self.mk_Multiverse(
                self.expand_and_flatten(value, cond, zcond))

            for expanded_cond, expanded_zcond, expanded_value in expanded_values:
                if expanded_value is None:
                    continue
                
                split_expanded_values = expanded_value.split()
                values.extend(split_expanded_values)

        return values