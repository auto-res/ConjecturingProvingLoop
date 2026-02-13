

theorem P1_pow {X : Type*} [TopologicalSpace X] {A : Set X} {n : ℕ} (hA : P1 A) : P1 ((fun x => x)^[n] '' A) := by
  -- The `n`-fold iterate of the identity map is the identity map.
  have h_iter : (Nat.iterate (fun x : X => x) n) = (fun x : X => x) := by
    funext x
    induction n with
    | zero      => rfl
    | succ n ih => simp [Nat.iterate, ih]
  -- Hence the image of `A` under this map is just `A` itself.
  have h_img : ((Nat.iterate (fun x : X => x) n) '' (A : Set X)) = A := by
    simpa [h_iter, Set.image_id]
  -- Rewriting with this equality, the goal reduces to `P1 A`.
  simpa [P1, h_img] using hA