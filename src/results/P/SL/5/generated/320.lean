

theorem interior_closure_iterate_from_interior {X : Type*} [TopologicalSpace X]
    (A : Set X) (n : ℕ) :
    Nat.iterate (fun S : Set X => interior (closure S)) (n.succ) (interior A) =
      interior (closure (interior A)) := by
  -- Define `f := interior ∘ closure`.
  let f : Set X → Set X := fun S => interior (closure S)
  -- `f` is idempotent.
  have hf_id : ∀ S : Set X, f (f S) = f S := by
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
    | succ m ih => simpa [Nat.iterate, hfix, ih]
  -- Rewriting the iterate so that it starts from the fixed point `f (interior A)`.
  have h_step :
      Nat.iterate f (n.succ) (interior A) =
        Nat.iterate f n (f (interior A)) := by
    simp [Nat.iterate]
  -- Since `f (interior A)` is a fixed point, the right‐hand side collapses.
  have h_iter :
      Nat.iterate f n (f (interior A)) = f (interior A) := by
    have hfix : f (f (interior A)) = f (interior A) := by
      simpa using hf_id (interior A)
    exact iterate_fixed hfix n
  -- Assemble the equalities and unfold `f`.
  simpa [f, h_step, h_iter]