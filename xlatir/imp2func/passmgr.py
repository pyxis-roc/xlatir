#!/usr/bin/env python3
#
# passmgr.py
# A simple pass-based framework for imp2func

import logging

logger = logging.getLogger(__name__)

#TODO: make this a dataclass?
class I2FConfig(object):
    linear = False     # Do not nest functions
    name_prefix = ''   # Use this as prefix to names of basic blocks
    dump_cfg = False
    debug = False
    loglevel = logging.WARNING

    prune_unreachable = False # Deprecated?
    error_on_non_exit_nodes = False # Deprecated?


    def __init__(self, linear = False, name_prefix = '', dump_cfg = False, debug = False,
                 loglevel = logging.WARNING):
        self.linear = linear
        self.name_prefix = name_prefix
        self.dump_cfg = dump_cfg
        self.debug = debug
        self.loglevel = loglevel

    def __setattr__(self, a, v):
        if not hasattr(self, a):
            raise AttributeError(f'Creating a new attribute {a} on I2FConfig is disallowed')
        else:
            super(I2FConfig, self).__setattr__(a, v)

class InterPassContext(object):
    filename = None # filename of XIR file, if loaded from file
    statements = None # XIR statements
    types = None # types for XIR variables on the LHS
    typed_backend = False # does the backend need types?
    output = None  # file handle to send output to
    backend = None # actual backend

    config = None # I2FConfig

    cfg = None # Control flow graph
    globalvars = None # set of global variables

    def __init__(self, config):
        self.config = config

    def __setattr__(self, a, v):
        if not hasattr(self, a):
            raise AttributeError(f'Creating a new attribute {a} on InterPassContext without declaring it is disallowed')
        else:
            super(InterPassContext, self).__setattr__(a, v)

class Pass(object):
    name = None

    def __init__(self):
        pass

    def run(self, ctx):
        raise NotImplementedError

class PassManager(object):
    def __init__(self, config, ctxclass = InterPassContext):
        self.ctx = ctxclass(config)
        self.passes = []

    def add(self, pass_):
        self.passes.append(pass_)

    def run_all(self):
        for p in self.passes:
            if not p.run(self.ctx):
                logger.error(f"Failed to run pass {p.__class__.__name__}.")
                return False

        return True
