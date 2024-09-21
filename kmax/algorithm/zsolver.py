from z3 import BoolVal, Solver

class ZSolver:
    def __init__(self):
        self.solver = Solver()

        self.T = BoolVal(True)
        self.F = BoolVal(False)

    def zcheck(self, f):
        self.solver.push()
        self.solver.add(f)
        ret = self.solver.check()
        self.solver.pop()
        return ret
