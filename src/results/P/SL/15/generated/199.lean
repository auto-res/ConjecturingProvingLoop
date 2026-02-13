

theorem interior_prod_nonempty_iff
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {A : Set X} {B : Set Y} :
    (interior (A ×ˢ B)).Nonempty ↔
      ((interior A).Nonempty ∧ (interior B).Nonempty) := by
  -- We use the characterization of the interior of a product.
  have h : interior (A ×ˢ B) = interior A ×ˢ interior B := by
    simpa using interior_prod_eq (s := A) (t := B)
  constructor
  · intro hNonempty
    rcases hNonempty with ⟨p, hp⟩
    have hp' : (p : X × Y) ∈ interior A ×ˢ interior B := by
      simpa [h] using hp
    rcases Set.mem_prod.1 hp' with ⟨hpA, hpB⟩
    exact ⟨⟨p.1, hpA⟩, ⟨p.2, hpB⟩⟩
  · rintro ⟨hIntA, hIntB⟩
    rcases hIntA with ⟨x, hx⟩
    rcases hIntB with ⟨y, hy⟩
    have hp : ((x, y) : X × Y) ∈ interior A ×ˢ interior B :=
      And.intro hx hy
    have : ((x, y) : X × Y) ∈ interior (A ×ˢ B) := by
      simpa [h] using hp
    exact ⟨(x, y), this⟩