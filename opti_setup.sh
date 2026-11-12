#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"

OPTIMATHSAT=optimathsat-1.7.4-linux-64-bit

# 1. System packages
sudo apt install -y g++ libgmp-dev python3-dev python3-venv

# # 2. Python virtual environment
# python3 -m venv .venv
# source .venv/bin/activate
# pip install -r requirements.txt

# 3. Download OptiMathSAT
mkdir -p solvers
if [ ! -d "solvers/$OPTIMATHSAT" ]; then
    curl -sL "https://optimathsat.disi.unitn.it/releases/optimathsat-1.7.4/$OPTIMATHSAT.tar.gz" | tar xz -C solvers
fi

# 4. Fix the bindings' import (_mathsat -> _optimathsat)
sed -i 's/^\(\s*\)from \. import _mathsat$/\1from . import _optimathsat as _mathsat/; s/^\(\s*\)import _mathsat$/\1import _optimathsat as _mathsat/' \
    "solvers/$OPTIMATHSAT/python/optimathsat.py"

# 5. Build the Python bindings
cd "solvers/$OPTIMATHSAT/python"
python3 setup.py build_ext --inplace
cd -
