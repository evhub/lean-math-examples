namespace util
    open function
    open classical (em prop_decidable)
    open classical (renaming some → unexists) (renaming some_spec → unexists_prop)
    local attribute [instance] prop_decidable

    -- classical logic:
    @[simp] theorem not_not_elim (P: Prop):
        ¬¬P ↔ P := begin
            apply iff.intro,
            {
                intro hnn,
                by_contra hn,
                apply hnn,
                exact hn,
            },
            {
                intros h hn,
                apply hn,
                exact h,
            },
        end

    theorem not_forall_not_elim {T: Type _} {P: T → Prop} (hnfa: ¬ ∀ x: T, ¬ P x):
        ∃ x: T, P x := begin
            by_contra hnex,
            apply hnfa,
            intro x,
            by_contra hnP,
            apply hnex,
            apply exists.intro x hnP,
        end

    @[simp] theorem not_and (A B: Prop):
        ¬(A ∧ B) ↔ ¬A ∨ ¬B := begin
            apply iff.intro,
            {
                intro hAB,
                cases (em A);
                cases (em B),
                {
                    apply false.elim,
                    apply hAB,
                    split;
                    assumption,
                },
                {
                    right,
                    assumption,
                },
                all_goals {
                    left,
                    assumption,
                },
            },
            {
                intros hor hand,
                cases hor,
                case or.inl {
                    apply hor,
                    exact hand.1,
                },
                case or.inr {
                    apply hor,
                    exact hand.2,
                },
            },
        end


    -- isempty:
    @[reducible] def isempty (A: Sort _):
        Prop := ¬ nonempty A

    theorem isempty.elim {A: Sort _} (h: isempty A) (a: A):
        ∀ {P: Prop}, P := begin
            intros,
            apply false.elim,
            apply h,
            split,
            exact a,
        end


    -- function classes:
    attribute [class] injective
    attribute [class] surjective
    attribute [class] bijective

    instance bijective_of_inj_sur {T T': Sort _} {f: T → T'} [hfi: injective f] [hfs: surjective f]:
        bijective f := (| hfi, hfs |)

    instance inj_of_bijective {T T': Sort _} {f: T → T'} [hf: bijective f]:
        injective f := hf.1

    instance sur_of_bijective {T T': Sort _} {f: T → T'} [hf: bijective f]:
        surjective f := hf.2


    -- inverses:
    class invertible {T T': Sort _} (f: T → T') :=
        (g: T' → T)
        (elim:
            ∀ x: T,
            g (f x) = x)

    @[reducible, inline] def inv {T T': Sort _} (f: T → T') [hf: invertible f]:
        T' → T := hf.g

    @[simp] theorem inv.elim {T T': Sort _} (f: T → T') [hf: invertible f]:
        ∀ x: T,
        inv f (f x) = x := by apply hf.elim

    instance inv.invertible {T T': Sort _} (f: T → T') [hfinv: invertible f] [hfsur: surjective f]:
        invertible (inv f) := begin
            split,
            show T → T', from f,
            intro x,
            apply exists.elim (hfsur x),
            intros y hy,
            rw [←hy],
            simp,
        end

    @[simp] theorem inv.elim_of_inv {T T': Sort _} (f: T → T') [hfinv: invertible f] [hfsur: surjective f]:
        inv (inv f) = f := by rw [inv.invertible]

    theorem inv.uniq {T T': Sort _} (f: T → T') [hfinv: invertible f] [hfsur: surjective f]:
        ∀ {g: T' → T},
        (∀ x: T, g (f x) = x) →
        g = inv f := begin
            intros g hg,
            funext,
            have hfsurx := hfsur x,
            apply exists.elim hfsurx,
            intros y hy,
            rw [←hy, hg y],
            rw [inv, hfinv.elim],
        end

    instance inv.surjective {T T': Sort _} (f: T → T') [hf: invertible f]:
        surjective (inv f) := begin
            intro x,
            apply exists.intro (f x),
            simp,
        end

    instance inv.injective {T T': Sort _} (f: T → T') [hfinv: invertible f] [hfsur: surjective f]:
        injective (inv f) := begin
            intros x y hxy,
            have hfx := hfsur x,
            have hfy := hfsur y,
            apply exists.elim hfx,
            intros a ha,
            apply exists.elim hfy,
            intros b hb,
            rw [←ha, ←hb] at *,
            simp at hxy,
            rw [hxy],
        end

    noncomputable def inj_inv {T T': Sort _} [hT: nonempty T] (f: T → T') (y: T'): T :=
        if h: ∃ x: T, f x = y then
            unexists h
        else
            choice hT

    noncomputable instance inj_inv.inv_of_inj{T T': Sort _} [hT: nonempty T] (f: T → T') [hf: injective f]:
        invertible f := {
            g := inj_inv f,
            elim := begin
                intros,
                rw [inj_inv],
                cases em (∃ (x' : T), f x' = f x),
                case or.inl {
                    rw [dif_pos h],
                    apply hf,
                    exact unexists_prop h,
                },
                case or.inr {
                    rw [dif_neg h],
                    apply false.elim,
                    apply h,
                    apply exists.intro x,
                    refl,
                },
            end,
        }


    -- id:
    instance id.bijective {T: Sort _}:
        bijective (@id T) := begin
            split,
            show injective id, by {
                intros x y h,
                simp at h,
                exact h,
            },
            show surjective id, by {
                intro x,
                apply exists.intro x,
                simp,
            },
        end

    instance id.invertible {T: Sort _}:
        invertible (@id T) := begin
            split,
            show T → T, from id,
            intro x,
            simp,
        end


    -- cast:
    @[simp] theorem cast_cast_elim {T T': Sort _} {x: T} (h: T = T') (h': T' = T):
        cast h' (cast h x) = x := begin
            cases h,
            refl,
        end

    theorem cast_eq_of_heq {T T': Sort _} {x: T} {x': T'}:
    x == x' →
    Σ' h: T = T',
    cast h x = x' := begin
        intro h,
        cases h,
        split,
        refl,
        refl,
    end

    theorem heq_of_cast_eq {T T': Sort _} {x: T} {x': T'} {h: T = T'}:
    cast h x = x' →
    x == x' := begin
        intro hcast,
        cases h,
        cases hcast,
        refl,
    end
end util
