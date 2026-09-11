module

import Std.Data.Iterators

/-! Tests for reverse iterators over ranges, arrays, and vectors. -/

open Std

#guard (Array.iterRev #[1, 2, 3]).toArray == #[3, 2, 1]
#guard (Vector.iterRev (Vector.ofFn fun i : Fin 3 => i.val)).toArray == #[2, 1, 0]

#guard ((2...=5).iterRev.take 4 |>.toArray) == #[5, 4, 3, 2]
#guard ((2...5).iterRev.take 3 |>.toArray) == #[4, 3, 2]
#guard ((2<...=5).iterRev.take 3 |>.toArray) == #[5, 4, 3]
#guard ((2<...5).iterRev.take 2 |>.toArray) == #[4, 3]
#guard (((2...*) : Rci (Fin 6)).iterRev.take 4 |>.toArray) == #[5, 4, 3, 2]
#guard (((2<...*) : Roi (Fin 6)).iterRev.take 3 |>.toArray) == #[5, 4, 3]
#guard (((*...=3) : Ric Nat).iterRev.take 4 |>.toArray) == #[3, 2, 1, 0]
#guard (((*...3) : Rio Nat).iterRev.take 3 |>.toArray) == #[2, 1, 0]
#guard (((*...*) : Rii (Fin 4)).iterRev.take 4 |>.toArray) == #[3, 2, 1, 0]
