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

    def get_typevars(self):
        raise NotImplementedError

class TyAlias(object):
    def __init__(self, name, value):
        self.name = name
        self.value = value

    def __str__(self):
        return f"TyAlias({self.name}, {self.value})"

    __repr__ = __str__

    def get_typevars(self):
        return []

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

    def get_typevars(self):
        return [self.name]


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

    def get_typevars(self):
        return []


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

    def get_typevars(self):
        return []

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

    def get_typevars(self):
        raise self.pty.get_typevars()


class TyProduct(TyTerm):
    def __init__(self, args):
        self.args = args

    def __str__(self):
        return f"{' * '.join([str(x) for x in self.args])}"

    __repr__ = __str__

    def copy(self, subst = None):
        arg_copies = [x.copy(subst) for x in self.args]

        return TyProduct(arg_copies)

    def get_typevars(self):
        out = []
        for a in self.args:
            out.extend(a.get_typevars())

        return out

class TyArray(TyTerm):
    def __init__(self, elt, sizes):
        self.elt = elt
        self.sizes = sizes # must be constants, don't support variables [could introduce TyValConstant]

    def __str__(self):
        return f"TyArray({self.elt}, [{', '.join([str(s) for s in self.sizes])}])"

    __repr__ = __str__

    def copy(self, subst = None):
        return TyArray(self.elt.copy(subst), list(self.sizes))

    def get_typevars(self):
        return self.elt.get_typevars()

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

    def get_typevars(self):
        out = self.ret.get_typevars()
        for a in self.args:
            out.extend(a.get_typevars())

        return out


# used in equations
class TyRecord(TyTerm):
    def __init__(self, name, fields_and_types):
        self.name = name
        # list of tuples of ('fieldname', fieldtype)
        self.fields_and_types = fields_and_types
        self.field_names = set([x[0] for x in self.fields_and_types])
        assert len(self.field_names) == len(self.fields_and_types), f"Possible duplicate field name."

    def __str__(self):
        n = self.name or '?'
        return f"TyRecord({n}, [{', '.join(['%s: %s' % (f, t) for f, t in self.fields_and_types])}])"

    __repr__ = __str__

    def copy(self, subst = None):
        fields_and_types_copies = [(x[0], x[1].copy(subst)) for x in self.fields_and_types]

        return TyRecord(self.name, fields_and_types_copies)

    def get_typevars(self):
        out = []
        for f, t in self.fields_and_types:
            out.extend(t.get_typevars())

        return out

# not sure if declarations should be tyterms
# this is closer to PolyTyDef
class RecordDecl(object):
    def __init__(self, name, fields_and_types, generic_tyvars = None):
        self.name = name
        # list of tuples of ('fieldname', fieldtype)
        self.fields_and_types = fields_and_types
        self.generic_tyvars = [] if generic_tyvars is None else generic_tyvars # list of tyvars.
        self.field_names = set([x[0] for x in self.fields_and_types])
        assert len(self.field_names) == len(self.fields_and_types), f"Possible duplicate field name"

    def __str__(self):
        return f"{self.name} [{', '.join(['%s: %s' % (f, t) for f, t in self.fields_and_types])}]"

    __repr__ = __str__

    def subst(self, decl, subst_values, record_decls):
        out_ft = []
        for (f, t) in decl.fields_and_types:
            if isinstance(t, TyVar):
                assert t.name in subst_values, f'Type variable {t.name} has no substitution'
                t = subst_values[t.name]
            elif isinstance(t, TyConstant):
                if t.value in record_decls:
                    raise NotImplementedError
                else:
                    t = t.copy()
            else:
                raise NotImplemented

            out_ft.append((f, t))

        return TyRecord(decl.name, out_ft)

    def get_tyrecord(self, record_decls, generic_subst = None):
        if len(self.generic_tyvars) > 0:
            assert generic_subst is not None, f'Generic substitutions needed for {self.name}'

            generic_subst = dict(zip([t.name for t in self.generic_tyvars], generic_subst))
            tyvars = set([t.name for t in self.generic_tyvars])
            missing = tyvars - set(generic_subst.keys())
            assert len(missing) == 0, f'{self.name} requires substitutions for all generic variables to produced TyRecord, missing substitutions for {missing}'
        else:
            assert generic_subst is None, f'Generic substitutions provided for {self.name}, which does not use Generic'

        return self.subst(self, generic_subst, record_decls)

    def copy(self, subst = None):
        fields_and_types_copies = [(x[0], x[1].copy(subst)) for x in self.fields_and_types]

        return RecordDecl(self.name, fields_and_types_copies)

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

    if isinstance(s, TyRecord) and isinstance(t, TyRecord):
        if s.name and t.name and s.name != t.name:
            print(f"Failed to unify records {s} and {t}, different structures!")
            return False

        nmemb1 = dict(s.fields_and_types)
        nmemb2 = dict(t.fields_and_types)
        nmemb = set(nmemb1.keys()).intersection(nmemb2.keys())

        for common in nmemb:
            if not unify(nmemb1[common], nmemb2[common]):
                print(f"Failed to unify common field {common} [when unifying records {s} and {t}]")
                return False



        name = s.name or t.name
        fields_and_types = [(n, nmemb1[n]) for n in nmemb]
        fields_and_types.extend([(k, nmemb1[k]) for k in nmemb1 if k not in nmemb])
        fields_and_types.extend([(k, nmemb2[k]) for k in nmemb2 if k not in nmemb])

        v = find(TyRecord(name, fields_and_types), reps, create_missing = True)
        union(s, v, reps)
        union(t, v, reps)

        return True

    if isinstance(s, TyVar) or isinstance(t, TyVar):
        union(s, t, reps)
        return True


    print("FAIL", s, t)
    return False


if __name__ == "__main__":
    test_PolyTyDef()
