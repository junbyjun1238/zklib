import Zklib.Core.NTT.Radix2.Correctness

universe u v w

namespace Zklib.Core

namespace Radix2

/--
A binary recursion tree for radix-2 FFT development.

Leaves correspond to base domains of size `1`, and internal nodes record the
recursive even/odd split. Keeping this tree separate from flattened output
arrays lets us formalize the recursion pattern before committing to a specific
output permutation.
-/
inductive FFTTree (alpha : Type u) : Type u where
  | leaf : alpha -> FFTTree alpha
  | node : FFTTree alpha -> FFTTree alpha -> FFTTree alpha

namespace FFTTree

variable {alpha : Type u}

def map {beta : Type v} (f : alpha -> beta) : Radix2.FFTTree alpha -> Radix2.FFTTree beta
  | .leaf a => .leaf (f a)
  | .node l r => .node (map f l) (map f r)

def left : Radix2.FFTTree alpha -> Option (Radix2.FFTTree alpha)
  | .leaf _ => none
  | .node l _ => some l

def right : Radix2.FFTTree alpha -> Option (Radix2.FFTTree alpha)
  | .leaf _ => none
  | .node _ r => some r

def leafCount : Radix2.FFTTree alpha -> Nat
  | .leaf _ => 1
  | .node l r => leafCount l + leafCount r

def flatten : Radix2.FFTTree alpha -> List alpha
  | .leaf a => [a]
  | .node l r => flatten l ++ flatten r

theorem map_map {beta : Type v} {gamma : Type w} (g : beta -> gamma) (f : alpha -> beta)
    (tree : Radix2.FFTTree alpha) :
    map g (map f tree) = map (Function.comp g f) tree := by
  induction tree with
  | leaf a =>
      rfl
  | node l r ihL ihR =>
      simp [map, ihL, ihR]

theorem map_congr {beta : Type v} {f g : alpha -> beta}
    (hfg : ∀ a, f a = g a) (tree : Radix2.FFTTree alpha) :
    map f tree = map g tree := by
  induction tree with
  | leaf a =>
      simp [map, hfg a]
  | node l r ihL ihR =>
      simp [map, ihL, ihR]

theorem leafCount_map {beta : Type v} (f : alpha -> beta) (tree : Radix2.FFTTree alpha) :
    leafCount (map f tree) = leafCount tree := by
  induction tree with
  | leaf a =>
      rfl
  | node l r ihL ihR =>
      simp [map, leafCount, ihL, ihR]

theorem flatten_map {beta : Type v} (f : alpha -> beta) (tree : Radix2.FFTTree alpha) :
    flatten (map f tree) = (flatten tree).map f := by
  induction tree with
  | leaf a =>
      rfl
  | node l r ihL ihR =>
      simp [map, flatten, ihL, ihR, List.map_append]

theorem flatten_length (tree : Radix2.FFTTree alpha) :
    (flatten tree).length = leafCount tree := by
  induction tree with
  | leaf a =>
      rfl
  | node l r ihL ihR =>
      simp [flatten, leafCount, ihL, ihR]

end FFTTree

end Radix2

namespace Radix2Domain

variable {F : Type*} [Field F]

/--
Auxiliary recursion for parity-split FFT development.

The parameter `k` tracks the expected radix-2 depth, and the equality witness
ties that depth to the domain's `logSize`.
-/
noncomputable def parityTreeAux :
    (k : Nat) ->
    (domain : Radix2Domain F) ->
    domain.logSize = k ->
    Polynomial F ->
    Radix2.FFTTree F
  | 0, domain, hk, poly =>
      Radix2.FFTTree.leaf (domain.toNTTSpec.transform poly (Fin.mk 0 domain.size_pos))
  | Nat.succ k, domain, hk, poly =>
      let hpos : 0 < domain.logSize := by simp [hk]
      Radix2.FFTTree.node
        (parityTreeAux k (domain.halfDomain hpos) (by simp [Radix2Domain.halfDomain, hk]) poly)
        (parityTreeAux k (domain.halfDomain hpos) (by simp [Radix2Domain.halfDomain, hk])
          (domain.twistPolynomial poly))

/--
The recursive radix-2 parity-split decomposition tree of a polynomial transform
over a radix-2 domain.
-/
noncomputable def parityTree (domain : Radix2Domain F) (poly : Polynomial F) :
    Radix2.FFTTree F :=
  parityTreeAux domain.logSize domain rfl poly

theorem parityTreeAux_zero (domain : Radix2Domain F) (hk : domain.logSize = 0)
    (poly : Polynomial F) :
    parityTreeAux 0 domain hk poly =
      Radix2.FFTTree.leaf (domain.toNTTSpec.transform poly (Fin.mk 0 domain.size_pos)) := by
  rfl

theorem parityTreeAux_succ (k : Nat) (domain : Radix2Domain F)
    (hk : domain.logSize = k + 1) (poly : Polynomial F) :
    parityTreeAux (k + 1) domain hk poly =
      Radix2.FFTTree.node
        (parityTreeAux k (domain.halfDomain (by simp [hk]))
          (by simp [Radix2Domain.halfDomain, hk]) poly)
        (parityTreeAux k (domain.halfDomain (by simp [hk]))
          (by simp [Radix2Domain.halfDomain, hk]) (domain.twistPolynomial poly)) := by
  rfl

end Radix2Domain

end Zklib.Core
