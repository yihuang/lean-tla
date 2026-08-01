/-! ## SetFn — Functional update at a single index

    `setFn f i x` returns a function that agrees with `f` everywhere
    except at index `i`, where it returns `x`. This is the standard
    pattern for modeling per-process state updates in parameterized
    protocols with `Fin n`-indexed local state.
-/

/-- Functional update: `setFn f i x j = if j = i then x else f j`. -/
def setFn {α : Type} {n : Nat} (f : Fin n → α) (i : Fin n) (x : α) : Fin n → α :=
  fun j => if j = i then x else f j

@[simp] theorem setFn_same {α} {n} (f : Fin n → α) (i : Fin n) (x : α) :
    setFn f i x i = x := by simp [setFn]

@[simp] theorem setFn_ne {α} {n} (f : Fin n → α) {i j : Fin n} (x : α) (h : j ≠ i) :
    setFn f i x j = f j := by simp [setFn, h]
