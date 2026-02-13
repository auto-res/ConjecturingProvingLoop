

theorem interior_closure_iterate {X : Type*} [TopologicalSpace X]
    (A : Set X) (n : ℕ) :
    Nat.iterate (fun S : Set X => interior (closure S)) (n.succ) A =
      interior (closure A) := by
  -- Define the idempotent function `f := interior ∘ closure`.
  let f : Set X → Set X := fun S => interior (closure S)
  -- `f` is idempotent.
  have h_idemp : ∀ S : Set X, f (f S) = f S := by
    intro S
    dsimp [f]
    simpa using Topology.interior_closure_idempotent (X := X) (A := S)
  -- A helper lemma: iterating an idempotent function on a fixed point
  -- leaves the point unchanged.
  have iterate_fixed {S : Set X} (hfix : f S = S) :
      ∀ m : ℕ, Nat.iterate f m S = S := by
    intro m
    induction m with
    | zero => simpa
    | succ m ih =>
        simp [Nat.iterate, hfix, ih]
  -- Main proof by cases on `n`.
  cases n with
  | zero =>
      -- `Nat.iterate f 1 A = f A`
      simp [Nat.iterate, f]
  | succ k =>
      -- First, iterate starting from the fixed point `f A`.
      have h1 : Nat.iterate f (Nat.succ k) (f A) = f A := by
        have hfix : f (f A) = f A := h_idemp A
        exact iterate_fixed hfix (Nat.succ k)
      -- Unfold one step of the iteration starting from `A`.
      have ht : Nat.iterate f (Nat.succ (Nat.succ k)) A = f A := by
        -- By definition of `Nat.iterate`.
        change Nat.iterate f (Nat.succ k) (f A) = f A
        simpa using h1
      -- Rewrite `f A` back to `interior (closure A)`.
      simpa [f] using ht