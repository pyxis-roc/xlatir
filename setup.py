from setuptools import setup, find_packages

setup(name='xlatir',
      version='0.1',
      packages=find_packages(),
      package_data={'xlatir.xir': ['stdlib/*.pyi']},
      scripts=['bin/imp2func_ssa.py',
               'bin/xir2x.py',
               'bin/xirconvert.py']
)
