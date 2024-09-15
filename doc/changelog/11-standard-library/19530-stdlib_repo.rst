- **Changed:**
  the development repository of Stdlib which is now
  `https://github.com/coq-community/stdlib-test/ <https://github.com/coq-community/stdlib-test/>`_.  TODO update before merge
  The recommended way to require
  Stdlib modules is `From Stdlib Require {Import,Export,}
  <LibraryModules>.`, except for `Byte` (use `From Stdlib.Strings` or
  `From Stdlib.Init`), `Tactics` (use `From Stdlib.Program` or `From
  Stdlib.Init`), `Tauto` (use `From Stdlib.micromega` of `From
  Stdlib.Init`) and `Wf` (use `From Stdlib.Program` or `From
  Stdlib.Init`). For backward compatibility with Coq <= 8.20, one can
  use `From Coq` instead of `From Stdlib`. The `coq` metapackage
  still depends on `coq-stdlib`. A new `rocq-init` package
  is added for users who don't want to depend on Stdlib
  (`#19530 <https://github.com/coq/coq/pull/19530>`_,
  by Pierre Roux, reviewed by Cyril Cohen).
