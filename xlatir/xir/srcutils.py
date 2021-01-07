#!/usr/bin/env python3
#
# srcutils.py
# Utilities for dealing with source files (include directories, etc.)

from pathlib import Path
import logging

logger = logging.getLogger(__name__)

class IncludeLocator(object):
    def __init__(self, include_dirs):
        include_dirs = [Path(p) for p in include_dirs]
        self.include_dirs = []

        for p in include_dirs:
            if not p.exists():
                logging.warning(f"{p} does not exist, ignoring")
            elif not p.is_dir():
                logging.warning(f"{p} is not a directory, ignoring")
            else:
                self.include_dirs.append(p)

    def locate(self, fname, no_error = False):
        f = Path(fname)

        if f.is_absolute():
            logging.info(f'Using absolute path {f}, not searching include directories')
            return f

        if not len(self.include_dirs):
            logging.debug(f'No include directories to search')
            return f

        for I in self.include_dirs:
            if (I / f).exists():
                logging.debug(f'Located {f} in {I}')
                return (I / f)

        if no_error:
            return None

        raise FileNotFoundError(f"{f} not found. Searched {', '.join([str(s) for s in self.include_dirs])}")
