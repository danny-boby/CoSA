from setuptools import setup, find_packages

long_description=\
"""================================
 CoSA: CoreIR Symbolic Analyzer
================================

CoSA is an SMT-based symbolic model checker for hardware design.

Supported Input Formats
=======================
* CoreIR (https://github.com/rdaly525/coreir)
* BTOR2 (https://github.com/Boolector/btor2tools)
* Symbolic Transition System
* Explicit Transition System

Supported Verifications
=======================
* Invariant Properties
* LTL Properties
* Proving capabilities
* Equivalence Checking
* Automated Lemma Extraction

CoSA relies on PySMT (http://www.pysmt.org), which is a solver
agnostic library to interface with SMT solvers.

For more information visit http://github.com/cristian-mattarei/CoSA
"""

setup(name='CoSA',
      version='0.1.2',
      description='CoreIR Symbolic Analyzer',
      long_description=long_description,
      url='http://github.com/cristian-mattarei/CoSA',
      author='Cristian Mattarei',
      author_email='cristian.mattarei@gmail.com',
      license='BSD',
      packages = find_packages(),
      include_package_data = True,
      install_requires=["six","pyparsing","pysmt","coreir"],
      entry_points={
          'console_scripts': [
              'CoSA = cosa.shell:main'
          ],
      },
      zip_safe=True)
