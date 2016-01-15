0.5
---
* Added flags for removing some dependencies.
* Support `doctests` when building to non-standard locations (such as when using `stack`.)
* Support `base-orphans`

0.4.4
-----
* `transformers 0.4` compatibility

0.4.3.1
-----
* Fixed builds with older versions of GHC

0.4.2
-------
* Added `Data.Distributive.Generic`.

0.4.1
-----
* `Control.Monad.Instances` is deprecated in GHC 7.8. Don't import it there.

0.4
---
* Added support for `Data.Tagged` and `Data.Proxy`.

0.3.1
-----
* Minor documentation fix

0.3
---
* Added instances for `Control.Applicative.Backwards` and `Data.Functor.Reverse` from `transformers` 0.3, taking them from `transformers-compat` if necessary for `transformers` 0.2

