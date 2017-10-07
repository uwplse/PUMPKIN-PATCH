This is a prototype plugin for finding patches by searching the difference
between two slightly different Coq proofs.

This is a research prototype, so it is definitely not production-ready.
For example, unquestionably the most difficult part of writing this prototype
was dealing with DeBruijn indexes (compiler hackers can probably sympathize),
so there are some workarounds related to indexing that may sometimes fail.

With that in mind, I hope that by getting it out into the open I can
contribute what I've learned so far. You can use it on the example proofs and
you can extend it if you are interested. Don't hesitate to reach out
if you have any questions.

# Building PUMPKIN

The plugin works for Coq 8.5pl3. If you would like to extend it to handle
Coq 8.6 or 8.7, go for it. I plan to support 8.7 in the future,
especially with the new plugin API.

## Plugin

cd plugin
make

# Using PUMPKIN

There are some example proofs you can try PUMPKIN on in the coq directory.
Just run coqc on those files to load them up.

You can look at the files to see how it is calling PUMPKIN, if you would
like to try it on some of your own proofs.
Also, if you look at patcher.ml4, there is some auxiliary commands you
can call to do things like invert terms and factor them into sequences
of terms. Just keep in mind that this is an initial proof-of-concept tool.

# Extending PUMPKIN

The entry-point to the code is patcher.ml4. You can add new commands there.
If you've never written a Coq plugin before, you might want to check out
and toy with my starter plugin first: https://github.com/uwplse/CoqAST/

The high-level patch finding procedure is in search.ml. From there, you
can extend the procedure or you can see what it calls out to and modify that.
There are also some useful debugging functions at the top of search.ml;
if you are modifying the tool, you may want to use those.

Minor note: .ml4 files don't appear to work with  a lot of emacs OCaml plugins.
You can run tuareg-mode manually on ml4 files.
