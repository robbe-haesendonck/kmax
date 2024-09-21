from dd.autoref import BDD

class KmaxBDD:
    def __init__(self) -> None:
        self.bdd = BDD()
        self.T = self.bdd_one()
        self.F = self.bdd_zero()

    def bdd_one(self):
        return self.bdd.true
        
    def bdd_zero(self):
        return self.bdd.false
    
    def bdd_ithvar(self, i):
        self.bdd.add_var(i)
        return self.bdd.var(i)
    
    def bdd_init(self):
        pass

    def bdd_destroy(self):
        pass

    def conj(self, a, b):
        return None if a is None or b is None else a & b
    
    def disj(self, a, b):
        return None if a is None or b is None else a | b
    
    def neg(self, a):
        return None if a is None else ~a
    
    def isfalse(self, b, z):
        return b == self.bdd.false
    
    def bdd_solutions(self, b):
        n = self.bdd.count(b)
        print(n)
        solutions = [d for d in self.bdd.pick_iter(b)]
        return solutions
    
    