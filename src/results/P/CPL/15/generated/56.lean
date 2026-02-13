

theorem P2_sigma {X : Type*} {Y : X → Type*} [∀ x, TopologicalSpace (Y x)] [TopologicalSpace (Σ x, Y x)] {A : Set (Σ x, Y x)} (h : ∀ x, P2 {p : Σ x, Y x | p.1 = x ∧ p ∈ A}) : P2 A := by
  intro p hpA
  -- `p` belongs to the fibre of `A` over `p.1`
  have hp_fibre :
      p ∈ {q : Σ x, Y x | q.1 = p.1 ∧ q ∈ (A : Set (Σ x, Y x))} := by
    exact And.intro rfl hpA
  -- Apply the hypothesis on that fibre
  have hp_in :
      p ∈ interior (closure (interior {q : Σ x, Y x | q.1 = p.1 ∧ q ∈ A})) :=
    (h (p.1)) hp_fibre
  -- The iterated interior of the fibre is contained in the one of `A`
  have h_subset :
      (interior (closure (interior {q : Σ x, Y x | q.1 = p.1 ∧ q ∈ A})) :
          Set (Σ x, Y x)) ⊆
        interior (closure (interior A)) := by
    -- first inclusion of sets
    have h_fibre_sub :
        ({q : Σ x, Y x | q.1 = p.1 ∧ q ∈ A} :
            Set (Σ x, Y x)) ⊆ A := by
      intro q hq
      exact hq.2
    have h_inner :
        (interior {q : Σ x, Y x | q.1 = p.1 ∧ q ∈ A} :
            Set (Σ x, Y x)) ⊆
          interior A :=
      interior_mono h_fibre_sub
    have h_closure :
        (closure (interior {q : Σ x, Y x | q.1 = p.1 ∧ q ∈ A}) :
            Set (Σ x, Y x)) ⊆
          closure (interior A) :=
      closure_mono h_inner
    exact interior_mono h_closure
  exact h_subset hp_in

theorem P3_iterate {X : Type*} [TopologicalSpace X] {A : Set X} (n : ℕ) (h : P3 A) : P3 ((fun x => x)^[n] '' A) := by
  -- The `n`-th iterate of the identity map is the identity itself.
  have h_iter : (Nat.iterate (fun x : X => x) n) = fun x : X => x := by
    funext x
    induction n with
    | zero      => rfl
    | succ n ih => simpa [Nat.iterate, ih]
  -- Hence the image of `A` under this map is just `A`.
  have h_img : (Nat.iterate (fun x : X => x) n) '' (A : Set X) = A := by
    simpa [h_iter, Set.image_id]
  -- Rewriting with this equality, the goal reduces to the given hypothesis.
  simpa [P3, h_img] using h

theorem P1_bUnion {X : Type*} [TopologicalSpace X] {ι : Sort*} {A : ι → Set X} (H : ∀ i, P1 (A i)) : P1 (⋃₀ {S | ∃ i, S = A i}) := by
  simpa using
    (P1_sUnion (X := X) (ℬ := {S : Set X | ∃ i, S = A i})
      (by
        intro S hS
        rcases hS with ⟨i, rfl⟩
        exact H i))

theorem P2_union_closed_dense {X : Type*} [TopologicalSpace X] {A B : Set X} (hA : IsClosed A) (hdB : closure (interior B) = Set.univ) : P2 (A ∪ B) := by
  intro x hx
  -- First, we show that the closure of the interior of the union is the whole
  -- space, using the density of `interior B`.
  have h_closure_eq : closure (interior (A ∪ B)) = (Set.univ : Set X) := by
    -- We prove the two inclusions separately.
    apply Set.Subset.antisymm
    · -- `closure (interior (A ∪ B)) ⊆ univ`
      intro y hy
      trivial
    · -- `univ ⊆ closure (interior (A ∪ B))`
      intro y hy
      -- `y` is in `closure (interior B)` because this set is `univ`.
      have h_in_closureB : (y : X) ∈ closure (interior B) := by
        simpa [hdB] using (Set.mem_univ y)
      -- `interior B ⊆ interior (A ∪ B)`, hence the same holds for closures.
      have h_subset :
          (closure (interior B) : Set X) ⊆
            closure (interior (A ∪ B)) :=
        closure_mono
          (interior_mono
            (by
              simpa using
                (Set.subset_union_right : (B : Set X) ⊆ A ∪ B)))
      exact h_subset h_in_closureB
  -- Since this closure is `univ`, its interior is also `univ`, and the goal
  -- follows immediately.
  have : (x : X) ∈ (Set.univ : Set X) := by
    trivial
  simpa [h_closure_eq, interior_univ] using this