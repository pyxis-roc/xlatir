from setuptools import setup, find_packages

setup(name='xlatir',
      version='0.1',
      packages=find_packages(),
      scripts=['bin/imp2func_ssa.py',
               'bin/xir2x.py',
               'bin/xirconvert.py']
)
