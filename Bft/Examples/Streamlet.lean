/-
Copyright (c) 2026 lean-tla contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The Streamlet case study, bundled

Umbrella module: import everything in `Bft/Examples/Streamlet/` — the
consistency core, the partially synchronous transport, the protocol layer,
the state-level liveness core, and the temporal wrapper. See
`Bft/Examples/Streamlet/README.md` for the layering.
-/
import Bft.Examples.Streamlet.Core
import Bft.Examples.Streamlet.Net
import Bft.Examples.Streamlet.Proto
import Bft.Examples.Streamlet.Liveness
import Bft.Examples.Streamlet.Temporal
