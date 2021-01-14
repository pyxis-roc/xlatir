#!/usr/bin/env python3
#
# xirsrc.py
# Load XIR source files in a uniform manner.

import ast
from .syntax import XIRSyntaxError, SourceInfo
from . import anno as xiranno
from . import usrlib
from . import xirtyping

class XIRSource(object):
    def load(self, srcfile):

        with open(srcfile, 'r') as f:
            # Load the XIR as Python code

            # TODO: use type comments?
            # TODO: use feature_version?
            contents = f.read()
            src = ast.parse(contents, srcfile)

        self.filename = srcfile
        self.srclines = contents.splitlines() # useful for error messages
        self.ast = src

    def _gen_source_info(self, node):
        return SourceInfo(filename=self.filename,
                          lineno=node.lineno if hasattr(node, 'lineno') else None,
                          col_offset=node.col_offset if hasattr(node, 'col_offset') else None,
                          srcline=self.srclines[node.lineno-1] if hasattr(node, 'lineno') else None)

    def _gen_syntax_error(self, message, node):
        return XIRSyntaxError(message,
                              self._gen_source_info(node))

    def parse(self, names = None):
        # We assume this is strict/plain XIR

        # Code: Import statements, Globals (for backward compat?),
        # TypeDecls, FunctionDefs (for types as well as semantics), later ClassDefs

        if names is None:
            names = set()

        if not isinstance(self.ast, ast.Module):
            raise self._gen_syntax_error(f"Expecting ast.Module, found {self.ast.__class__.__name__}", self.ast)

        fdefs = {}
        usrdecls = {}
        gl = {}
        d2t = usrlib.Decl2Type(xirtyping)

        for s in self.ast.body:
            if isinstance(s, ast.FunctionDef):
                if s.name in names:
                    # technically, not a syntax error ...
                    raise self._gen_syntax_error(f"{s.name} is duplicated", s)

                names.add(s.name)

                if xiranno.has_anno(s, xiranno.XIR_IGNORE):
                    continue

                if usrlib.is_xir_declaration(s):
                    usrdecls[s.name] = d2t.from_FunctionDef(s)
                else:
                    fdefs[s.name] = s
            elif isinstance(s, ast.Assign):
                # at global level, only support simple assignments
                if not (len(s.targets) == 1 and isinstance(s.targets[0], ast.Name)):
                    raise self._gen_syntax_error(f"Only simple var = value assignments supported.", s)

                names.add(s.targets[0].id)

                # This is either a typedecl/a type alias, or constant assignment

                if usrlib.is_xir_type_decl(s):
                    d2t.add_type_decl(s)
                else:
                    #TODO: we need to restrict this so that it is gl =
                    # constant [transitively], so we can strictly disambiguate between
                    # typedecls and constants, and catch syntax errors?
                    #
                    # re-examine why this was needed, since only PTX uses it.
                    gl[s.targets[0].id] = s
            elif isinstance(s, ast.AnnAssign):
                # not sure this is needed
                raise NotImplementedError
            elif isinstance(s, (ast.Import, ast.ImportFrom)):
                # TODO: set up namespaces, etc.
                pass
            else:
                raise self._gen_syntax_error(f"Unsupported statement {s.__class__.__name__}", s)

        return (gl, fdefs, usrdecls, d2t)
