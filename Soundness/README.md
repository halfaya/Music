# Logical Soundness

## Files

Note that `N` refers to version `N` of the music.

* agda (directory of source code)
* LogicalSoundness`N`.pdf (score)
* LogicalSoundness`N`.mp3 (MP3 audio)

## Notes

This was the final composition assignment for Bellevue College Music
212. It is an attempt to audibly represent the structure of Lemma 4.3 of
[Decidability of conversion for type theory in type theory](https://dl.acm.org/doi/10.1145/3158111).


Brief notes on the versions created so far follow. Each can be recreated by pulling the appropriate
"version `N`" commit from github. You may need to pull an older version of MusicTools from the same
time as well.

1. Single line piano, 3 levels of recursion. Had a bug in which speed was doubled far more often than intended.
2. Single line piano, 3 levels of recursion. Fixed the bug from version 1 and made other small changes.
3. Four line piano, 2 levels of recursion. Lines are folded together not following the proof structure.
4. Four line piano/organ, 2 levels of recursion. Version 3 for two pianos and two organs.

## Instructions

To build requires the following dependencies, with all Agda libraries installed
[locally](https://agda.readthedocs.io/en/latest/tools/package-system.html).
* [Agda](https://github.com/agda/agda) post-2.6.2, supporting `--erased-cubical`
* [GHC](https://www.haskell.org/ghc/) I am using 8.10.2, but other versions likely work.
* [MusicTools](https://github.com/halfaya/MusicTools) latest version
* [agda-stdlib](https://github.com/agda/agda-stdlib) matching the Agda version
* [cubical](https://github.com/agda/cubical) matching the Agda version
* [logrel-mltt](https://github.com/mr-ohman/logrel-mltt) I'm using a version whose latest commit is Feb 22, 2021, but
  other versions probably work. Note that I had to add the line `name: logrel-mltt` to `logrel-mltt.agda-lib` to
  make it work properly as a library.

To compile and run, go to the `agda` directory,
modify the `file` variable of `SMain.agda` to be an appropriate local file location, and then in a shell run
```
agda -c SMain.agda
./SMain
```
This will create the MIDI file you have specified in the `file` variable.
