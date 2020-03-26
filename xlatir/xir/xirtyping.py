class TyEqn(object):
    def __init__(self, lhs, rhs, src=None):
        self.lhs = lhs
        self.rhs = rhs
        self.src = src

    def __str__(self):
        return f"{self.lhs} = {self.rhs} # {self.src if self.src else ''}"

    def __repr__(self):
        return f"TyEqn({self.lhs}, {self.rhs}, {self.src})"

class TyVar(object):
    def __init__(self, name):
        self.name = name

    def __eq__(self, other):
        return (self is other) or (isinstance(other, TyVar) and other.name == self.name)

    def __str__(self):
        return f"TyVar({self.name})"

    __repr__ = __str__

# temporary for now
class TyVarLiteral(TyVar):
    def __init__(self, name, literal):
        super(TyVarLiteral, self).__init__(name)
        self.literal = literal

    def __eq__(self, other):
        #name is the value of the literal...
        return (self is other) or (isinstance(other, TyVar) and other.name == self.name)

    def __str__(self):
        return f"TyVarLiteral({self.name}, {self.literal})"

    __repr__ = __str__

class TyConstant(object):
    def __init__(self, value):
        self.value = value

    def __eq__(self, other):
        return self is other or isinstance(other, TyConstant) and other.value == self.value
    def __str__(self):
        return f"TyConstant({self.value})"

    __repr__ = __str__

class TyApp(object):
    def __init__(self, ret, args):
        self.ret = ret
        self.args = args

    def __str__(self):
        return f"TyApp({self.ret}, [{', '.join([str(x) for x in self.args])}]"

    __repr__ = __str__
