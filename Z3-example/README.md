Download Z3 at https://github.com/Z3Prover/z3/releases

Unzipped it into a directory called `MYZ3`, then follow these instructions to run the example:

Running this example on Windows:
```
set PATH=%PATH%;MYZ3\bin
set PYTHONPATH=MYZ3\bin\python
python z3ex.py
```

Running this example on Linux:
```
export LD_LIBRARY_PATH=$LD_LIBRARY_PATH:MYZ3/bin
export PYTHONPATH=MYZ3/bin/python
python z3ex.py
```

Running this example on macOS:
```
export PATH=$PATH:MYZ3/bin
export PYTHONPATH=MYZ3/bin/python
python z3ex.py
```
