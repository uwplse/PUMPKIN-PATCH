#!/bin/sh

coqc coq/SoundDecompiler.v > coq/sound_decompiler.out
diff coq/sound_decompiler.out coq/sound_regression.txt
