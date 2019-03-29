
-----------------------
Instructions on how to compile the Coq code, extract the Haskell code and run the Haskell code.
-----------------------

What files are included?

  - Our Coq code is found in the "coq_code" directory.
  - Haskell code that we have extracted previously can be found in the "Haskell_code" directory. You can disregard this if you wish to extract the code yourself using the Coq code (recommended; see the command "make run" below).
  - There is one Haskell file called "Main.hs" that was written for pretty printing and we have included a copy in both the "coq_code" and "Haskell_code" directories.
  - "Examples.txt" gives a few different examples of very simple Sahlqvist formulae and how to input them using the syntax specified in "Main.hs".

Once you have navigated to the "coq_code" directory, you can execute the following commands on the command line:

  - make run
    This will take you straight to the verified Haskell program where you can compute via the function "corr" the first-order correspondent when given a very simple Sahlqvist modal formula. See "Examples.txt" for an explanation of how to compute the correspondent using correct syntax. It compiles all the required Coq *.v files, extracts the Haskell files from "vsSahlq_extraction.vo" and runs ghci on "Main.hs". This is essentially "make vsSahlq_extraction.vo" followed by "make run_hs" (see below).

  - make vsSahlq_extraction.vo
    This compiles all the required *.v files and extracts the Haskell code into that directory. 

  - make run_hs
    This runs ghci on "Main.hs" where you can compute via the function "corr" the first-order correspondent when given a very simple Sahlqvist modal formula. 

  - make clean
    If you are on a unix machine, this removes all of the compiled *.vo, *.glob and extracted *.hs files (not including "Main.hs" that we wrote for pretty printing).

  - make clean_win
    If you are on a windows machine, this removes all of the compiled *.vo, *.glob and extracted *.hs files (not including "Main.hs" that we wrote for pretty printing).
