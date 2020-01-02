# Preducer
A precision reducer for Fortran77 files

## Why?
We needed a way to downgrade the precision in F77 files, to observe the
differences in roundoff.

## How?
Preducer is a Python script that parses F77 files, finds all subroutines and
functions contained therein, and changes all their variables from double to
single precision. The new routines/functions will have the original name with
\_sp appended.  For example, `subroutine foo` becomes `subroutine foo_sp`. To
make it easier to call these new routines, a wrapper will be created that has
the original name (in this case `foo`) and all arguments still have the
original precision. This wrapper will cast all inputs to single precision, then
call the low precision routine (`foo_sp`) using single precision inputs, and
finally casts the results to double precision.

## Installation
Preducer imports the following packages, pip install them as necessary:
```
fparser, sys, re, textwrap
```

## Usage
The script can be directly called from the command line as
```
./preducer FILENAME.f
./preducer FILENAME.f SUBROUTINENAME
./preducer -verbose FILENAME.f
./preducer -verbose FILENAME.f SUBROUTINENAME
```

## CUTEST
We used preducer as part of a Julia wrapper for CUTEst optimization problems.
The Julia wrapper uses SIFDECODER to create a F77 file, after which we call
Preducer to modify the precision. Preducer is tested on the files that
SIFDECODER creates, and may break in various ways on other input files.
The Julia code was modified to call Preducer and pass verbosity flags
appropriately, the result is also included in this repository.

## CUTEST installation
If you plan to use Preducer with the Julia CUTEST package (see below), it is
additionally necessary to define an environment variable called "PREDUCER"
holding the Preducer directory. In the `CUTEST.jl` file, the follwing lines
must be added directly below `if isfile("ELFUN.f")`:
```
      if "-preduce" in args
        preducenv = ENV["PREDUCER"]
        preducer = "$preducenv/preducer.py"
        if verbose
          preducer = ["$preducenv/preducer.py","-verbose"]
        end
        run(`$preducer ELFUN.f`)
        run(`mv ELFUN_preduced.f ELFUN.f`)
        run(`$preducer EXTER.f`)
        run(`mv EXTER_preduced.f EXTER.f`)
        run(`$preducer GROUP.f`)
        run(`mv GROUP_preduced.f GROUP.f`)
        run(`$preducer RANGE.f`)
        run(`mv RANGE_preduced.f RANGE.f`)
      end
```

## CUTEST usage
Use Preducer from Julia's CUTEST as follows:
```
nlp = CUTEstModel("ROSENBR", "-preduce")
nlp = CUTEstModel("ROSENBR", verbose=true, "-preduce")
```
