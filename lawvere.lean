import .util

namespace lawvere
    open function
    open classical (em)

    open util
    universes u v

    -- properties of functions:
    structure func_prop :=
        (P: Π {A B: Sort _}, (A → B) → Prop)
        (elim_comp:
            ∀ {A B C: Sort _},
            ∀ {f: B → C},
            ∀ {g: A → B},
            P f →
            P g →
            P (f ∘ g))
        (elim_id:
            ∀ {A: Sort _},
            (∃ {B: Sort _} (f: A → B), P f) →
            P (λ x: A, x))
        (elim_pair:
            ∀ {A B C: Sort _},
            ∀ {f: A → B},
            ∀ {g: A → C},
            P f →
            P g →
            P (λ a: A, (f a, g a)))
        (elim_unpair:
            ∀ {A B C: Sort _},
            ∀ {f: A → Σ' f: B → C, P f},
            P f →
            P (λ aa: A × B, (f aa.1).1 aa.2))

    instance func_prop.has_coe_to_fun:
        has_coe_to_fun func_prop := {
            F := λ P, Π {A B: Sort _}, (A → B) → Prop,
            coe := λ P, P.P,
        }

    @[simp] theorem func_prop.coe_elim (P: func_prop) {A B: Sort _} (f: A → B):
        P f = P.P f := rfl


    -- functions with properties:
    @[reducible] def func (A B: Sort _) (P: func_prop): Sort _ :=
        Σ' f: A → B,
        P f

    @[reducible] def func.f {A B: Sort _} {P: func_prop} (f: func A B P):
        A → B := f.1

    @[reducible] def func.prop {A B: Sort _} {P: func_prop} (f: func A B P):
        P f.f := f.2

    instance func.has_coe_to_fun (A B: Sort _) (P: func_prop):
        has_coe_to_fun (func A B P) := {
            F := λ f, A → B,
            coe := λ f, f.f,
        }

    @[simp] theorem func.coe_elim {A B: Sort _} {P: func_prop} (f: func A B P) (x: A):
        f x = f.f x := rfl


    -- lawvere's theorem:
    theorem func_prop.elim_diag (P: func_prop):
        ∀ {A B: Sort _},
        ∀ {f: func A (func A B P) P},
        P f →
        P (λ a: A, f a a) :=
            assume A B: Sort _,
            assume f: func A (func A B P) P,
            assume Pf: P f,
            let f': func (A × A) B P := (|
                λ aa: A × A, f aa.1 aa.2,
                begin
                    apply P.elim_unpair,
                    exact Pf,
                end,
            |) in
            begin
                have hf': ∀ a a': A, f' (a, a') = f a a', by {
                    intros,
                    refl,
                },
                have hfunc: (λ a, f a a) = (λ a, f' (a, a)), by {
                    funext,
                    rw [hf'],
                },
                rw [hfunc],
                apply P.elim_comp,
                exact f'.prop,
                apply P.elim_pair;
                apply P.elim_id,
                all_goals {
                    apply exists.intro (func A B P),
                    apply exists.intro f.f,
                    exact f.prop,
                },
            end

    @[reducible] def func_prop.fixpt_prop (P: func_prop) (A: Sort _): Prop :=
        ∀ h: func A A P,
        ∃ a: A,
        a = h a

    theorem lawvere {X: Sort _} {A: Sort _} {P: func_prop}:
        ∀ {f: func X (func X A P) P},
        surjective f →
        P.fixpt_prop A :=
            assume f: func X (func X A P) P,
            assume sur_f: surjective f,
            assume h: func A A P,
            let g: func X A P := (|
                λ x: X, h (f x x),
                begin
                    simp,
                    apply P.elim_comp,
                    exact h.prop,
                    apply P.elim_diag,
                    exact f.prop,
                end,
            |) in
            exists.elim (sur_f g) (
                assume x: X,
                assume hfx: f x = g,
                let a: A := f x x in
                exists.intro a (
                    calc a = f x x:     rfl
                    ... = (f x).f x:    rfl
                    ... = g.f x:        by rw [hfx]
                    ... = h (f x x):    rfl
                    ... = h a:          rfl
                )
            )


    -- simple lawvere:
    @[reducible] def fixpt_prop (A: Sort _): Prop :=
        ∀ h: A → A,
        ∃ a: A,
        a = h a

    def triv_prop: func_prop := {
        P := λ A B f, true,
        elim_comp := begin
            intros,
            trivial,
        end,
        elim_id := begin
            intros,
            trivial,
        end,
        elim_pair := begin
            intros,
            trivial,
        end,
        elim_unpair := begin
            intros,
            trivial,
        end,
    }

    @[reducible] def triv_func (A B: Sort _): Sort _ :=
        func A B triv_prop

    @[reducible] def triv_func.mk {A B: Sort _} (f: A → B):
        triv_func A B := (|
            f,
            trivial,
        |)

    theorem simple_lawvere_base {X: Sort _} {A: Sort _}:
        ∀ {f: triv_func X (triv_func X A)},
        surjective f →
        fixpt_prop A := begin
            intros f sur_f h,
            have law_f := lawvere sur_f,
            have fix_h := law_f (triv_func.mk h),
            apply exists.elim fix_h,
            intros x hx,
            apply exists.intro x,
            simp at hx,
            rw [triv_func.mk, func.f] at hx,
            simp at hx,
            exact hx,
        end

    theorem simple_lawvere {X: Type (max u v)} {A: Type (max u v)}:
        ∀ {f: X → X → A},
        surjective f →
        fixpt_prop A :=
            assume f: X → X → A,
            assume sur_f: surjective f,
            let f' := triv_func.mk (λ x1: X, triv_func.mk (λ x2: X, f x1 x2)) in
            have sur_f': surjective f', by {
                intro h,
                apply exists.elim (sur_f h.f),
                intros x hx,
                apply exists.intro x,
                have f'f: f'.f = λ x1: X, triv_func.mk (λ x2: X, f x1 x2) := rfl,
                simp [f'f, hx],
                induction h,
                simp [func.f, triv_func.mk],
            },
            simple_lawvere_base sur_f'


    -- domain/codomain properties:
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

    def dom_cod_prop (P: Π A B: Sort _, Prop)
        (Ptrans: transitive P)
        (Psemirefl:
            ∀ {A B: Sort _},
            P A B →
            P A A)
        (Pprod:
            ∀ {A B C: Sort _},
            P A B →
            P A C →
            P A (B × C))
        (Punprod:
            ∀ {A B C D: Sort _},
            P A D →
            (isempty A ∨ P B C) →
            P (A × B) C):
        func_prop := {
            P := λ A B f, P A B,
            elim_comp := begin
                intros A B C f g hBC hAB,
                exact Ptrans hAB hBC,
            end,
            elim_id := begin
                intros A hex,
                apply exists.elim hex,
                intros B hB,
                apply exists.elim hB,
                intros f hA,
                apply Psemirefl,
                exact hA,
            end,
            elim_pair := begin
                intros A B C f g hA hA',
                apply Pprod,
                exact hA,
                exact hA',
            end,
            elim_unpair := begin
                intros A B C f hA,
                apply Punprod,
                exact hA,
                cases em (nonempty A),
                case or.inl {
                    apply h.elim,
                    intro a,
                    have hBC := (f a).2,
                    right,
                    exact hBC,
                },
                case or.inr {
                    left,
                    exact h,
                },
            end,
        }


    -- product of:
    inductive product_of (X: Sort _): Sort _ → Prop
    | exact: product_of X
    | prod {A B: Sort _} (hA: product_of A) (hB: product_of B): product_of (A × B)

    @[refl] theorem product_of.refl (A: Sort _):
        product_of A A := product_of.exact A

    @[simp] theorem nonempty_product (A B: Sort _):
        nonempty (A × B) ↔ nonempty A ∧ nonempty B := begin
            apply iff.intro,
            {
                intro hAB,
                apply hAB.elim,
                intro ab,
                split,
                exact nonempty.intro ab.1,
                exact nonempty.intro ab.2,
            },
            {
                intro hAB,
                apply hAB.2.elim,
                apply hAB.1.elim,
                intros a b,
                exact nonempty.intro (a, b),
            },
        end

    @[simp] theorem isempty_product (A B: Sort _):
        isempty (A × B) ↔ isempty A ∨ isempty B := by simp [isempty]

    theorem product_of.nonempty {X A: Sort _} (hA: product_of X A):
        nonempty A ↔ nonempty X := begin
            apply iff.intro,
            {
                intro hne,
                apply hne.elim,
                intro a,
                induction hA,
                case product_of.exact {
                    apply nonempty.intro a,
                },
                case product_of.prod {
                    simp at hne,
                    apply hA_ih_hA,
                    exact hne.1,
                    exact a.1,
                },
            },
            {
                intro hne,
                induction hA,
                case product_of.exact {
                    exact hne,
                },
                case product_of.prod {
                    simp,
                    split;
                    assumption,
                },
            },
        end


    -- restricted domain:
    def restricted_dom {dom: Sort _} (hdom: nonempty dom):
        func_prop := begin
            apply dom_cod_prop (λ A B, product_of dom A),
            {
                intros A B C hA hB,
                exact hA,
            },
            {
                intros A B hA,
                exact hA,
            },
            {
                intros A B C hA hA',
                exact hA,
            },
            {
                intros A B C D hA hB,
                simp at hB,
                cases hB,
                case or.inl {
                    apply false.elim,
                    apply hB,
                    induction hA,
                    case product_of.exact {
                        exact hdom,
                    },
                    case product_of.prod {
                        simp at *,
                        split,
                        {
                            cases hB,
                            case or.inl {
                                apply hA_ih_hA,
                                contradiction,
                            },
                            case or.inr {
                                exact hA_hA.nonempty.mpr hdom,
                            },
                        },
                        {
                            cases hB,
                            case or.inl {
                                apply hA_ih_hB,
                                have hB' := hA_ih_hA hB,
                                contradiction,
                            },
                            case or.inr {
                                exact hA_hB.nonempty.mpr hdom,
                            },
                        },
                    },
                },
                case or.inr {
                    apply product_of.prod;
                    assumption,
                },
            },
        end
end lawvere
