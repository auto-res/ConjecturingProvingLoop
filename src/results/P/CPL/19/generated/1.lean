

theorem P3_of_dense {X : Type*} [TopologicalSpace X] {A : Set X} (hA : closure A = Set.univ) : P3 A := by
  intro x hx
  -- The interior of the closure is the whole space, since the closure is the whole space.
  have h_int : interior (closure A) = (Set.univ : Set X) := by
    simpa [hA, interior_univ]
  -- Every point is in the whole space.
  have hx_univ : x ∈ (Set.univ : Set X) := by
    simp
  -- Hence the desired inclusion holds.
  simpa [h_int] using hx_univ

theorem P2_union {X : Type*} [TopologicalSpace X] {A B : Set X} : P2 A → P2 B → P2 (A ∪ B) := by
  intro hP2A hP2B
  intro x hx
  cases hx with
  | inl hxA =>
      -- `x` comes from `A`
      have hx_in : x ∈ interior (closure (interior A)) := hP2A hxA
      -- `interior A` is contained in `interior (A ∪ B)`
      have hsubset_int : interior A ⊆ interior (A ∪ B) := by
        apply interior_mono
        intro y hy
        exact Or.inl hy
      -- Taking closures preserves inclusions
      have hsubset_closure :
          closure (interior A) ⊆ closure (interior (A ∪ B)) :=
        closure_mono hsubset_int
      -- Taking interiors preserves inclusions as well
      have hsubset :
          interior (closure (interior A)) ⊆
            interior (closure (interior (A ∪ B))) :=
        interior_mono hsubset_closure
      exact hsubset hx_in
  | inr hxB =>
      -- `x` comes from `B`
      have hx_in : x ∈ interior (closure (interior B)) := hP2B hxB
      -- `interior B` is contained in `interior (A ∪ B)`
      have hsubset_int : interior B ⊆ interior (A ∪ B) := by
        apply interior_mono
        intro y hy
        exact Or.inr hy
      -- Taking closures preserves inclusions
      have hsubset_closure :
          closure (interior B) ⊆ closure (interior (A ∪ B)) :=
        closure_mono hsubset_int
      -- Taking interiors preserves inclusions as well
      have hsubset :
          interior (closure (interior B)) ⊆
            interior (closure (interior (A ∪ B))) :=
        interior_mono hsubset_closure
      exact hsubset hx_in

theorem P3_union {X : Type*} [TopologicalSpace X] {A B : Set X} : P3 A → P3 B → P3 (A ∪ B) := by
  intro hP3A hP3B
  intro x hx
  cases hx with
  | inl hxA =>
      -- `x` comes from `A`
      have hx_int : x ∈ interior (closure A) := hP3A hxA
      -- `closure A` is contained in `closure (A ∪ B)`
      have hsubset_closure : closure A ⊆ closure (A ∪ B) := by
        apply closure_mono
        intro y hy
        exact Or.inl hy
      -- hence their interiors are related
      have hsubset : interior (closure A) ⊆ interior (closure (A ∪ B)) :=
        interior_mono hsubset_closure
      exact hsubset hx_int
  | inr hxB =>
      -- `x` comes from `B`
      have hx_int : x ∈ interior (closure B) := hP3B hxB
      -- `closure B` is contained in `closure (A ∪ B)`
      have hsubset_closure : closure B ⊆ closure (A ∪ B) := by
        apply closure_mono
        intro y hy
        exact Or.inr hy
      -- hence their interiors are related
      have hsubset : interior (closure B) ⊆ interior (closure (A ∪ B)) :=
        interior_mono hsubset_closure
      exact hsubset hx_int

theorem P2_interior {X : Type*} [TopologicalSpace X] {A : Set X} : P2 A → P2 (interior A) := by
  intro hP2
  intro x hx
  have hxA : x ∈ (A) := (interior_subset : interior A ⊆ A) hx
  have hmem : x ∈ interior (closure (interior A)) := hP2 hxA
  simpa [interior_interior] using hmem