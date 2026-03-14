import Zklib.Core.NTT.Radix2.Semantics
import Zklib.Core.NTT.Radix2.Representation
import Zklib.Core.NTT.Radix2.Tree
import Zklib.Core.NTT.Radix2.IndexTree
import Zklib.Core.NTT.Radix2.Flatten
import Zklib.Core.NTT.Radix2.BitReversal
import Zklib.Core.NTT.Radix2.FFT
import Zklib.Core.NTT.Radix2.FFTCorrectness
import Zklib.Core.NTT.Radix2.Natural
import Zklib.Core.NTT.Radix2.NaturalCorrectness
import Zklib.Core.NTT.Radix2.NaturalList
import Zklib.Core.NTT.Radix2.NaturalListCorrectness
import Zklib.Core.NTT.Radix2.NaturalArray
import Zklib.Core.NTT.Radix2.NaturalArrayCorrectness
import Zklib.Core.NTT.Radix2.CosetFFT
import Zklib.Core.NTT.Radix2.CosetTree
import Zklib.Core.NTT.Radix2.CosetFlatten
import Zklib.Core.NTT.Radix2.CosetFFTCorrectness
import Zklib.Core.NTT.Radix2.CosetNatural
import Zklib.Core.NTT.Radix2.CosetNaturalCorrectness
import Zklib.Core.NTT.Radix2.CosetNaturalList
import Zklib.Core.NTT.Radix2.CosetNaturalListCorrectness
import Zklib.Core.NTT.Radix2.CosetNaturalArray
import Zklib.Core.NTT.Radix2.CosetNaturalArrayCorrectness

/-!
`Zklib.Core.NTT.Radix2.Algorithms` contains concrete radix-2 FFT realizations
and theorems that identify those implementations with the semantic transform.

This is the representation-heavy layer: tree orderings, bit-reversal views,
natural-order recursions, and list/array implementations all live here rather
than in the semantic NTT surface.
-/
