class TyEqn(object):
    def __init__(self, lhs, rhs, src=None):
        self.lhs = lhs
        self.rhs = rhs
        self.src = src

    def __str__(self):
        return f"{self.lhs} = {self.rhs} # {self.src if self.src else ''}"

    def __repr__(self):
        return f"TyEqn({self.lhs}, {self.rhs}, {self.src})"

class TyTerm(object):
    def copy(self, subst = None):
        raise NotImplementedError

class TyVar(TyTerm):
    def __init__(self, name):
        self.name = name

    def __eq__(self, other):
        return (self is other) or (isinstance(other, TyVar) and other.name == self.name)

    def __str__(self):
        return f"TyVar({self.name})"

    __repr__ = __str__

    def copy(self, subst = None):
        if subst and self.name in subst:
            return TyVar(subst[self.name])
        else:
            return TyVar(self.name)

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

class TyConstant(TyTerm):
    def __init__(self, value):
        self.value = value

    def __eq__(self, other):
        return self is other or isinstance(other, TyConstant) and other.value == self.value

    def __str__(self):
        return f"TyConstant({self.value})"

    __repr__ = __str__

    def copy(self, subst = None):
        return TyConstant(self.value)

class TyApp(TyTerm):
    def __init__(self, ret, args):
        self.ret = ret
        self.args = args

    def __str__(self):
        return f"TyApp({self.ret}, [{', '.join([str(x) for x in self.args])}]"

    __repr__ = __str__

    def copy(self, subst = None):
        arg_copies = [x.copy(subst) for x in self.args]
        ret_new = self.ret.copy(subst)

        return TyApp(ret_new, arg_copies)


class PolyTyDef(object):
    def __init__(self, uqvars, typedef):
        self.uqvars = uqvars
        self.typedef = typedef

    def __str__(self):
        if self.uqvars:
            uqvars = f"forall {', '.join(self.uqvars)}: "
        else:
            uqvars = ""

        return f"{uqvars}{self.typedef}"

    def __repr__(self):
        return f"PolyTyDef({self.uqvars}, {self.typedef}"

    def get(self, subst = None):
        if self.uqvars and subst is None:
            raise ValueError("subst is None: Can't have an empty substitution for polymorphic typedef")

        return self.typedef.copy(subst)

def test_PolyTyDef():
    add_tydef = PolyTyDef(["gamma"],
                          TyApp(TyVar("gamma"), [TyVar("gamma"), TyVar("gamma")]))

    print(add_tydef)

    try:
        print(add_tydef.get())
    except ValueError:
        pass

    print(add_tydef.get({'gamma': 'gamma0'}))

if __name__ == "__main__":
    test_PolyTyDef()
