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

# temporary for now: note this behaves like TyVar
class TyVarLiteral(TyVar):
    def __init__(self, name, literal):
        super(TyVarLiteral, self).__init__(name)
        self.literal = literal

    def __eq__(self, other):
        #name is the value of the literal...
        return (self is other) or (isinstance(other, TyVarLiteral) and other.name == self.name)

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

class TyPtr(TyTerm):
    def __init__(self, pointee_type):
        self.pty = pointee_type

    def __eq__(self, other):
        #name is the value of the literal...
        return (self is other) or (isinstance(other, TyPtr) and other.pty == self.pty)

    def __str__(self):
        return f"TyPtr({self.pty})"

    __repr__ = __str__

    def copy(self, subst = None):
        pty_copy = self.pty.copy(subst)

        return TyPtr(pty_copy)

class TyProduct(TyTerm):
    def __init__(self, args):
        self.args = args

    def __str__(self):
        return f"{' * '.join([str(x) for x in self.args])}"

    __repr__ = __str__

    def copy(self, subst = None):
        arg_copies = [x.copy(subst) for x in self.args]

        return TyProduct(arg_copies)

class TyArray(TyTerm):
    def __init__(self, elt, sizes):
        self.elt = elt
        self.sizes = sizes # must be constants, don't support variables [could introduce TyValConstant]

    def __str__(self):
        return f"TyArray({self.elt}, [{', '.join([str(s) for s in self.sizes])}])"

    __repr__ = __str__

    def copy(self, subst = None):
        return TyArray(self.elt.copy(subst), list(self.sizes))

# rewrite this in terms of TyProduct?
class TyApp(TyTerm):
    def __init__(self, ret, args):
        self.ret = ret
        self.args = args

    def __str__(self):
        return f"TyApp({self.ret}, [{', '.join([str(x) for x in self.args])}])"

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

        # first make a copy
        cp = self.typedef.copy(subst)

        #TODO: we should get rid of the duplicates
        return cp

def test_PolyTyDef():
    add_tydef = PolyTyDef(["gamma"],
                          TyApp(TyVar("gamma"), [TyVar("gamma"), TyVar("gamma")]))

    print(add_tydef)

    try:
        print(add_tydef.get())
    except ValueError:
        pass

    print(add_tydef.get({'gamma': 'gamma0'}))

def find(n, reps, create_missing = False):
    #TODO: this depends on the key being "immutable", and fails for TyArray
    key = str(n)

    if key not in reps:
        if create_missing:
            reps[key] = n
        else:
            raise KeyError(f"{key} not found in representatives")

    if reps[key] is not n:
        r = find(reps[key], reps, create_missing)
        reps[key] = r

    return reps[key]

def union(s, t, reps):
    #print("\t unioning", s, reps[str(s)], t, reps[str(t)])
    if isinstance(s, TyConstant):
        reps[str(t)] = reps[str(s)]
    elif isinstance(t, TyConstant):
        reps[str(s)] = reps[str(t)]
    elif isinstance(s, TyVarLiteral): #TODO: introduced for shift?
        reps[str(t)] = reps[str(s)]
    elif isinstance(t, TyVarLiteral): #TODO: introduce for shift?
        reps[str(s)] = reps[str(t)]
    elif isinstance(s, TyProduct):   #TODO: setp_q
        reps[str(t)] = reps[str(s)]
    elif isinstance(t, TyProduct):
        reps[str(s)] = reps[str(t)]
    elif isinstance(s, TyArray):   #TODO: dpXa
        reps[str(t)] = reps[str(s)]
    elif isinstance(t, TyArray):
        reps[str(s)] = reps[str(t)]
    elif isinstance(s, TyApp):
        reps[str(t)] = reps[str(s)]
    elif isinstance(t, TyApp):
        reps[str(s)] = reps[str(t)]
    else:
        reps[str(s)] = reps[str(t)]

    #print("\t\t result", s, reps[str(s)], t, reps[str(t)])

# dragon book, figure 6.32, suitably adapted, but should be made simpler
def unify(m, n, reps = None):
    if reps is None:
        reps = {}

    s = find(m, reps, create_missing = True)
    t = find(n, reps, create_missing = True)

    #print(f"{m} {s}")
    #print(f"{n} {t}")

    if s is t: return True

    if isinstance(s, TyConstant) and isinstance(t, TyConstant):
        if s == t:
            return True

        # unify carryflag with both u and s
        if s.value == "carryflag" or t.value == "carryflag":
            notcarryflag = s.value if s.value != "carryflag" else t.value
            if notcarryflag[0] == "u" or notcarryflag[0] == "s":
                return True

        # uX = bX
        if (s.value[0] == "u" and t.value[0] == "b") or (s.value[0] == "b" and t.value[0] == "u"):
            if s.value[1:] == t.value[1:]:
                return True

    if isinstance(s, TyApp) and isinstance(t, TyApp):
        if len(s.args) == len(t.args):
            union(s, t, reps)
            if not unify(s.ret, t.ret, reps):
                return False

            for a, b in zip(s.args, t.args):
                if not unify(a, b, reps):
                    print(f"Failed to unify {a} and {b} [when unifying applications {s} and {t}]")
                    return False

            return True
        else:
            return False

    if isinstance(s, TyProduct) and isinstance(t, TyProduct):
        if len(s.args) == len(t.args):
            union(s, t, reps)
            for a, b in zip(s.args, t.args):
                if not unify(a, b, reps):
                    print(f"Failed to unify {a} and {b} [when unifying {s} and {t}]")
                    return False

            return True
        else:
            return False

    if isinstance(s, TyArray) and isinstance(t, TyArray):
        if len(s.sizes) == len(t.sizes):
            union(s, t, reps)
            if not unify(s.elt, t.elt, reps):
                print(f"Failed to unify {s.elt} and {e.elt} [when unifying arrays {s} and {t}]")
                return False

            for i, (a, b) in enumerate(zip(s.sizes, t.sizes)):
                # hmm ... avoid solving for sizes
                if a == '?':
                    a = b
                    s.sizes[i] = a
                elif b == '?':
                    b = a
                    t.sizes[i] = b

                if a != b:
                    print(f"Failed to unify, non-matching sizes {a} and {b} [when unifying arrays {s} and {t}]")
                    return False

            return True
        else:
            return False

    if isinstance(s, TyVar) or isinstance(t, TyVar):
        union(s, t, reps)
        return True


    print("FAIL", s, t)
    return False


if __name__ == "__main__":
    test_PolyTyDef()
