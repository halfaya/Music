# Logical Soundness

## Files

Note that `N` refers to version `N` of the music.

* agda (directory of source code)
* LogicalSoundness`N`.pdf (score)
* LogicalSoundness`N`.mp3 (MP3 audio)

## Notes and Instructions

This was the final composition assignment for Bellevue College Music
212. It is an attempt audibly represent the structure of Lemma 4.3 of
[Decidability of conversion for type theory in type theory](https://dl.acm.org/doi/10.1145/3158111).

It requires the [MusicTools](https://github.com/halfaya/MusicTools) library,
and recent enough versions of Agda (post-2.6.2, supporting `--erased-cubical`)
and GHC (I am using 8.10.2, but many other versions likely work). To compile and run, go to the `agda` directory,
modify the `file` variable of `SMain.agda` to be an appropriate local file location, and then in a shell run
```
agda -c SMain.agda
./SMain
```
This will create the MIDI file you have specified in the `file` variable.

Brief notes on the versions created so far follow. Each can be recreated by pulling the appropriate
"version `N`" commit from github.

1. Single line piano, 3 levels of recursion. Had a bug in which speed was doubled far more often than intended.
2. Single line piano, 3 levels of recursion. Fixed the bug from version 1 and other small changes.
3. Four line piano, 2 levels of recursion. Lines are folded together not following the proof structure.
