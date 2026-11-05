import Lean
import LoopsFormal

/-!
# Every delayed five-vertex clone is primitive

The original directed graph has the six edge occurrences
  e → a, e → b, b → a, a → f, f → c, c → e
and the cross section is {e,f}.  Cloning **both** gates into chains of
length n gives 2*n+5 vertices.  In the cyclic order

 e₀, ..., eₙ, b, a, f₀, ..., fₙ, c,

all edges are the ordinary forward cycle edges, plus one extra edge
from eₙ directly to a (skipping b).  That is the precise graph encoded
below.

A directed graph is primitive if one common length T admits a walk from
EVERY vertex to EVERY vertex.  We construct T explicitly for all n.
This proof does not yet identify the graph's first-return matrix with
the separate [[0, 2], [1, 0]] computation in LoopsFormal.lean.
-/

namespace LoopsFormal.CloneGraph

def size (n : Nat) : Nat := 2 * n + 5

abbrev Vertex (n : Nat) := Fin (size n)

def hub (n : Nat) : Vertex n :=
  ⟨0, by dsimp [size]; omega⟩

def lastVertex (n : Nat) : Vertex n :=
  ⟨size n - 1, by dsimp [size]; omega⟩

def tip (n : Nat) : Vertex n :=
  ⟨n, by dsimp [size]; omega⟩

def afterTip (n : Nat) : Vertex n :=
  ⟨n + 2, by dsimp [size]; omega⟩

/-- Clockwise cycle step, wrap step, or the single one-vertex shortcut. -/
def Edge (n : Nat) (u v : Vertex n) : Prop :=
  v.val = u.val + 1 ∨
  (u.val + 1 = size n ∧ v.val = 0) ∨
  (u.val = n ∧ v.val = n + 2)

/-- A directed walk with exactly the stated number of edges. -/
inductive Walk (n : Nat) : Nat → Vertex n → Vertex n → Prop where
  | nil (v : Vertex n) : Walk n 0 v v
  | edge {u v : Vertex n} (h : Edge n u v) : Walk n 1 u v
  | append {i j : Nat} {u v w : Vertex n} :
      Walk n i u v → Walk n j v w → Walk n (i + j) u w

/-- Walking forward along the ordinary chain, without wrapping. -/
theorem forward (n i : Nat) (hi : i < size n) :
    ∀ k (hk : i + k < size n),
      Walk n k (⟨i, hi⟩ : Vertex n)
        (⟨i + k, hk⟩ : Vertex n) := by
  intro k
  induction k with
  | zero =>
      intro hk
      simpa using (Walk.nil (⟨i, hi⟩ : Vertex n))
  | succ k ih =>
      intro hk
      have hprev : i + k < size n := by omega
      have hstep :
          Edge n (⟨i + k, hprev⟩ : Vertex n)
            (⟨i + (k + 1), hk⟩ : Vertex n) := by
        left
        dsimp
        omega
      have hpath := Walk.append (ih hprev) (Walk.edge hstep)
      simpa [Nat.succ_eq_add_one, Nat.add_assoc] using hpath

/-- From the zero vertex, walking forward v.val steps reaches v. -/
theorem fromHub (n : Nat) (v : Vertex n) :
    Walk n v.val (hub n) v := by
  have hzero : 0 < size n := by dsimp [size]; omega
  have hv : 0 + v.val < size n := by simpa using v.isLt
  simpa [hub] using (forward n 0 hzero v.val hv)

/-- From any vertex, continue around the ordinary cycle to the hub. -/
theorem toHub (n : Nat) (v : Vertex n) :
    Walk n (size n - v.val) v (hub n) := by
  have hbefore : v.val + (size n - 1 - v.val) < size n := by
    have hv := v.isLt
    dsimp [size] at *
    omega
  have hbase := forward n v.val v.isLt
    (size n - 1 - v.val) hbefore
  have hlast :
      (⟨v.val + (size n - 1 - v.val), hbefore⟩ : Vertex n)
        = lastVertex n := by
    apply Fin.ext
    dsimp [lastVertex]
    have hv := v.isLt
    dsimp [size] at *
    omega
  rw [hlast] at hbase
  have hwrap : Edge n (lastVertex n) (hub n) := by
    right
    left
    constructor
    · dsimp [lastVertex, size]
    · rfl
  have hpath := Walk.append hbase (Walk.edge hwrap)
  have hlength :
      (size n - 1 - v.val) + 1 = size n - v.val := by
    have hv := v.isLt
    dsimp [size] at *
    omega
  rw [hlength] at hpath
  exact hpath

/-- The full forward cycle has length 2*n+5. -/
theorem longLoop (n : Nat) :
    Walk n (size n) (hub n) (hub n) := by
  simpa [hub] using (toHub n (hub n))

/-- Taking the shortcut eₙ→a gives a loop of length 2*n+4. -/
theorem shortLoop (n : Nat) :
    Walk n (size n - 1) (hub n) (hub n) := by
  have hchord : Edge n (tip n) (afterTip n) := by
    right
    right
    constructor <;> rfl
  have pfirst : Walk n n (hub n) (tip n) := by
    simpa [tip] using (fromHub n (tip n))
  have plast : Walk n (size n - (n + 2)) (afterTip n) (hub n) := by
    simpa [afterTip] using (toHub n (afterTip n))
  have hpath := Walk.append
    (Walk.append pfirst (Walk.edge hchord)) plast
  have hlength :
      n + 1 + (size n - (n + 2)) = size n - 1 := by
    dsimp [size]
    omega
  rw [hlength] at hpath
  exact hpath

/-- A closed walk can be repeated any prescribed number of times. -/
theorem repeatLoop {n length : Nat} {v : Vertex n}
    (p : Walk n length v v) (times : Nat) :
    Walk n (times * length) v v := by
  induction times with
  | zero =>
      simpa using (Walk.nil v)
  | succ k ih =>
      have hpath := Walk.append p ih
      simpa [Nat.succ_mul, Nat.add_assoc, Nat.add_comm] using hpath

/-- A single, explicit exponent has walks between every ordered pair of
    vertices.  The common length is T=(2L)*L where L=2*n+5.

    Let a=L-u.val, b=v.val, d=a+b and M=2L.  Every source can
    reach the hub in a steps, and the hub can reach every target
    in b steps.  Run d short cycles (each saves 1 from L), plus
    M-d long cycles.  The total length is
      a+d(L-1)+(M-d)L+b = ML.
-/
theorem every_clone_is_primitive (n : Nat) :
    ∃ T : Nat, ∀ u v : Vertex n, Walk n T u v := by
  let L : Nat := size n
  let M : Nat := 2 * L
  refine ⟨M * L, ?_⟩
  intro u v
  let a : Nat := L - u.val
  let b : Nat := v.val
  let d : Nat := a + b
  have hd : d ≤ M := by
    have hu := u.isLt
    have hv := v.isLt
    dsimp [d, a, b, M, L, size] at *
    omega
  have hsave : d * (L - 1) + d = d * L := by
    have hL : (L - 1) + 1 = L := by
      dsimp [L, size]
    calc
      d * (L - 1) + d = d * (L - 1) + d * 1 := by simp
      _ = d * ((L - 1) + 1) := by rw [Nat.mul_add]
      _ = d * L := by rw [hL]
  have hrest : (M - d) * L + d * L = M * L := by
    rw [← Nat.add_mul]
    have hM : M - d + d = M := Nat.sub_add_cancel hd
    rw [hM]
  have hlength :
      a + d * (L - 1) + (M - d) * L + b = M * L := by
    calc
      a + d * (L - 1) + (M - d) * L + b
          = (M - d) * L + (d * (L - 1) + d) := by
              dsimp [d]
              omega
      _ = (M - d) * L + d * L := by rw [hsave]
      _ = M * L := hrest
  have hpath : Walk n
      (a + d * (L - 1) + (M - d) * L + b) u v :=
    Walk.append
      (Walk.append
        (Walk.append (toHub n u) (repeatLoop (shortLoop n) d))
        (repeatLoop (longLoop n) (M - d)))
      (fromHub n v)
  rw [hlength] at hpath
  exact hpath

end LoopsFormal.CloneGraph
