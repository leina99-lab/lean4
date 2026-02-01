# Lean4 완전 정복 가이드 — 제4-1편

## 명제 논리 완전 정복: Rosen 이산수학 1장 기반

---

# 제4-1편: 명제 논리 (Propositional Logic)

> **교재**: Kenneth H. Rosen, "Discrete Mathematics and Its Applications" 8판
> **범위**: 1장 - 기초: 논리와 증명 (1.1절 명제 논리)

---

## 4-1.0 이 장에서 배우는 것

이 장에서는 다음을 학습한다:

1. **명제**(Proposition)가 무엇인지
2. **논리 연산자**: 부정(¬), 논리곱(∧), 논리합(∨), 조건문(→), 상호조건문(↔)
3. Lean4에서 명제를 어떻게 표현하고 증명하는지
4. **진리표**(Truth Table)를 Bool로 계산하기
5. **증명**(Proof)을 Prop으로 작성하기

---

## 4-1.1 명제란 무엇인가?

### 정의

**명제**(Proposition)란 **참 또는 거짓 중 하나**를 명확히 판정할 수 있는 **선언적 문장**이다.

### 명제인 것 vs 명제가 아닌 것

| 문장 | 명제인가? | 이유 |
|------|----------|------|
| "워싱턴 D.C.는 미국의 수도이다" | ✓ 명제 | 참/거짓 판정 가능 (참) |
| "1 + 1 = 2" | ✓ 명제 | 참/거짓 판정 가능 (참) |
| "2 + 2 = 3" | ✓ 명제 | 참/거짓 판정 가능 (거짓) |
| "몇 시입니까?" | ✗ 명제 아님 | 의문문, 참/거짓 판정 불가 |
| "이것을 읽어라" | ✗ 명제 아님 | 명령문, 참/거짓 판정 불가 |
| "x + 1 = 2" | ✗ 명제 아님 | x 값에 따라 달라짐 (명제 함수) |

### Lean에서 명제

Lean에서 명제는 `Prop` 타입이다.

```lean
-- 구체적인 명제 (진리값이 정해짐)
#check (2 + 2 = 4)        -- Prop (참인 명제)
#check (2 + 2 = 5)        -- Prop (거짓인 명제)

-- 명제 변수 선언
variable (P Q R : Prop)   -- P, Q, R은 명제 변수
```

---

## 4-1.2 부정 (Negation): ¬

### 정의

명제 p의 **부정**(Negation)은 "p가 아니다"이며, **¬p** (또는 ⁻p, ~p)로 표기한다.

### 진리표

| p | ¬p |
|---|-----|
| T | F |
| F | T |

**핵심**: ¬p의 진리값은 p의 진리값의 **반대**이다.

### Lean에서 부정

Lean에서 `¬p`는 실제로 `p → False`로 **정의**되어 있다.

```lean
-- ¬p의 정의를 확인해보자
#print Not
-- 출력: def Not : Prop → Prop := fun a => a → False
```

**이게 무슨 뜻일까?**

```
¬p = "p가 아니다"
   = "p라고 가정하면 모순(False)이 생긴다"
   = "p → False"
```

**왜 이렇게 정의할까?**

수학에서 "p가 아니다"를 증명하는 가장 일반적인 방법은:
1. p가 참이라고 **가정**한다
2. 그 가정에서 **모순**을 이끌어낸다
3. 따라서 p는 거짓이다 (귀류법)

이 과정이 바로 `p → False`이다!

```lean
-- ¬p와 (p → False)가 정의상 같음을 확인
example (p : Prop) : ¬p = (p → False) := by
  rfl  -- rfl이 성공한다 = 정의상 완전히 같다는 뜻!
```

**`rfl`이 왜 성공하는가?**

`rfl`(reflexivity, 반사성)은 "양쪽이 **정의상 같을 때**" 성공한다.
- `¬p`는 `p → False`의 **축약 표기**일 뿐이다
- Lean 내부에서 `¬p`를 보면 자동으로 `p → False`로 펼친다
- 따라서 `¬p = (p → False)`는 `(p → False) = (p → False)`와 같다
- 이건 당연히 `rfl`로 증명된다!

**실용적 의미:**

```lean
-- hnp : ¬p 가 있으면, 이것을 함수처럼 쓸 수 있다!
-- hnp : p → False 와 같으니까

-- hp : p 가 있으면
-- hnp hp : False 가 된다 (p를 넣으면 False가 나옴)
```

### 전술 복습 (3편, 4편 참조)

>  **참고**: 이 장에서 사용하는 전술들은 **제3편**과 **제4편**에서 자세히 배웠다. 여기서는 간단히 복습한다.

**논리 전술** (3편):

| 전술 | 하는 일 | 상세 설명 |
|------|---------|----------|
| `intro h` | 가정 도입 (→, ∀에 사용) | 3편 3.8절 |
| `exact h` | 목표와 정확히 일치하는 증거 제시 | 3편 3.9절 |
| `apply h` | 정리/가정 적용하여 목표 축소 | 3편 3.10절 |
| `cases h with` | 가정 분해 (∧, ∨에 사용) | 3편 3.11~3.12절 |
| `constructor` | 목표 분해 (∧, ↔에 사용) | 3편 3.11절 |
| `left` / `right` | ∨ 증명 시 왼쪽/오른쪽 선택 | 3편 3.12절 |

**계산 전술** (4편):

| 전술 | 하는 일 | 상세 설명 |
|------|---------|----------|
| `rw [h]` | 등식으로 치환 | 4편 4.1~4.7절 |
| `simp` | 자동 단순화 | 4편 4.8절 |
| `ring` | 다항식 등식 자동 증명 | 4편 4.9절 |
| `omega` | 정수 부등식/등식 자동 증명 | 4편 4.10절 |
| `decide` | 결정 가능한 명제 계산 | 4편 4.13절 |
| `by_cases` | 경우 분류 (고전 논리) | 아래 설명 |

**처음 배우는 분은 3편과 4편을 먼저 학습하시오!**

### by_cases 전술 배우기

**`by_cases`**는 **고전 논리**(classical logic)에서 사용하는 전술이다.

**언제 쓰는가?**
- 어떤 명제 P에 대해 "P이거나 ¬P이다"로 경우를 나눌 때
- 배중률(excluded middle)을 사용할 때

**문법:**

```lean
by_cases hp : p
-- 이제 두 경우로 나뉜다:
--   경우 1: hp : p (p가 참)
--   경우 2: hp : ¬p (p가 거짓)
```

**예시:**

```lean
-- (p → q) ↔ (¬p ∨ q) 증명의 한 부분
example (p q : Prop) (h : p → q) : ¬p ∨ q := by
  by_cases hp : p
  -- 경우 1: hp : p (p가 참)
  · right
    exact h hp
  -- 경우 2: hp : ¬p (p가 거짓)
  · left
    exact hp
```

**시각적으로:**

```
by_cases hp : p
       ↓
┌─────────────────┬─────────────────┐
│ 경우 1          │ 경우 2          │
│ hp : p          │ hp : ¬p         │
│ (p가 참이라 가정)│ (p가 거짓이라 가정)│
└─────────────────┴─────────────────┘
```

### 연습 1: 부정의 정의 이해

```lean
-- 문제: ¬p가 참이고, p가 참이면 모순(False)임을 보여라
example (p : Prop) (hnp : ¬p) (hp : p) : False := by
  sorry  -- 빈칸을 채우시오
```

<details>
<summary>힌트 보기</summary>

`¬p`는 `p → False`와 같다. 즉, `hnp`는 "p가 참이면 False"라는 함수이다.
`hnp`에 `hp`를 적용하면 된다.

</details>

<details>
<summary>정답 보기</summary>

```lean
example (p : Prop) (hnp : ¬p) (hp : p) : False := by
  exact hnp hp
  -- 또는
  -- apply hnp
  -- exact hp
```

**설명**: 
- `hnp : ¬p`는 `hnp : p → False`와 같다
- `hp : p`이므로
- `hnp hp : False`가 된다

</details>

---

## 4-1.3 논리곱 (Conjunction): ∧

### 정의

명제 p와 q의 **논리곱**(Conjunction)은 "p 그리고 q"이며, **p ∧ q**로 표기한다.

### 진리표

| p | q | p ∧ q |
|---|---|-------|
| T | T | T |
| T | F | F |
| F | T | F |
| F | F | F |

**핵심**: p ∧ q는 **둘 다 참**일 때만 참이다.

### Lean에서 논리곱

```lean
-- p ∧ q를 증명하려면: 두 부분을 각각 증명해야 함 (constructor)
-- p ∧ q를 사용하려면: .left로 p를, .right로 q를 꺼냄

-- 구조:
-- ⟨hp, hq⟩ : p ∧ q   (hp : p, hq : q를 묶음)
-- h.left : p          (h : p ∧ q에서 왼쪽 꺼냄)
-- h.right : q         (h : p ∧ q에서 오른쪽 꺼냄)
```

>  `constructor`, `.left`, `.right`의 상세 설명은 **3편 3.11절** 참조

### 연습 2: 논리곱 증명하기

```lean
-- 문제: p와 q가 참이면 p ∧ q도 참임을 보여라
example (p q : Prop) (hp : p) (hq : q) : p ∧ q := by
  sorry  -- 빈칸을 채우시오
```

<details>
<summary>힌트 보기</summary>

`constructor` 전술을 사용하면 목표가 두 개로 나뉜다.
또는 `⟨hp, hq⟩`로 직접 쌍을 만들 수 있다. (⟨는 `\langle`, ⟩는 `\rangle`)

</details>

<details>
<summary>정답 보기</summary>

```lean
example (p q : Prop) (hp : p) (hq : q) : p ∧ q := by
  constructor
  · exact hp
  · exact hq

-- 또는 한 줄로:
-- exact ⟨hp, hq⟩
```

**설명**:
- `constructor` 전술은 `∧` 목표를 두 개의 하위 목표로 분해한다
- 첫 번째 목표: `p` 증명 → `exact hp`
- 두 번째 목표: `q` 증명 → `exact hq`

</details>

>  `.left`, `.right`, `obtain`의 상세 설명은 **3편 3.11절** 참조

### 연습 3: 논리곱에서 꺼내기

```lean
-- 문제: p ∧ q가 참이면 p도 참임을 보여라
example (p q : Prop) (h : p ∧ q) : p := by
  sorry  -- 빈칸을 채우시오
```

<details>
<summary>힌트 보기</summary>

`h.left` 또는 `h.1`로 왼쪽 부분을 꺼낼 수 있다.

</details>

<details>
<summary>정답 보기</summary>

```lean
example (p q : Prop) (h : p ∧ q) : p := by
  exact h.left

-- 또는:
-- exact h.1
-- 또는:
-- obtain ⟨hp, hq⟩ := h
-- exact hp
```

**설명**:
- `h : p ∧ q`에서 `h.left`는 `p`의 증거를 꺼낸다
- `h.right`는 `q`의 증거를 꺼낸다

</details>

### 연습 4: 논리곱의 교환법칙

```lean
-- 문제: p ∧ q이면 q ∧ p임을 보여라
example (p q : Prop) (h : p ∧ q) : q ∧ p := by
  sorry  -- 빈칸을 채우시오
```

<details>
<summary>힌트 보기</summary>

1. `h`에서 `p`와 `q`를 각각 꺼낸다
2. 순서를 바꿔서 다시 묶는다

</details>

<details>
<summary>정답 보기</summary>

```lean
example (p q : Prop) (h : p ∧ q) : q ∧ p := by
  constructor
  · exact h.right
  · exact h.left

-- 또는 한 줄로:
-- exact ⟨h.right, h.left⟩
-- 또는:
-- exact ⟨h.2, h.1⟩
```

**설명**:
- `h.right`로 `q`를 꺼내고
- `h.left`로 `p`를 꺼낸 후
- `⟨q의 증거, p의 증거⟩`로 `q ∧ p`를 구성한다

</details>

---

## 4-1.4 논리합 (Disjunction): ∨

### 정의

명제 p와 q의 **논리합**(Disjunction)은 "p 또는 q"이며, **p ∨ q**로 표기한다.

### 진리표

| p | q | p ∨ q |
|---|---|-------|
| T | T | T |
| T | F | T |
| F | T | T |
| F | F | F |

**핵심**: p ∨ q는 **둘 중 하나라도 참**이면 참이다. (포괄적 논리합)

### Lean에서 논리합

```lean
-- p ∨ q를 증명하려면: 둘 중 하나만 증명하면 됨 (left 또는 right)
-- p ∨ q를 사용하려면: 두 경우로 나눠서 처리 (cases)

-- Or.inl hp : p ∨ q   (p가 참이므로)
-- Or.inr hq : p ∨ q   (q가 참이므로)
```

>  `left`, `right`, `cases`의 상세 설명은 **3편 3.12절** 참조

### 연습 5: 왼쪽으로 논리합 증명

```lean
-- 문제: p가 참이면 p ∨ q도 참임을 보여라
example (p q : Prop) (hp : p) : p ∨ q := by
  sorry  -- 빈칸을 채우시오
```

<details>
<summary>힌트 보기</summary>

`left` 전술을 사용하면 "왼쪽을 선택한다"는 의미이다.
또는 `Or.inl hp`를 직접 사용할 수 있다.

</details>

<details>
<summary>정답 보기</summary>

```lean
example (p q : Prop) (hp : p) : p ∨ q := by
  left
  exact hp

-- 또는 한 줄로:
-- exact Or.inl hp
```

**설명**:
- `left` 전술은 "p ∨ q를 증명하기 위해 p를 증명하겠다"는 선언이다
- 그 후 `exact hp`로 p를 증명한다

</details>

### 연습 6: 오른쪽으로 논리합 증명

```lean
-- 문제: q가 참이면 p ∨ q도 참임을 보여라
example (p q : Prop) (hq : q) : p ∨ q := by
  sorry  -- 빈칸을 채우시오
```

<details>
<summary>힌트 보기</summary>

`right` 전술을 사용하면 "오른쪽을 선택한다"는 의미이다.

</details>

<details>
<summary>정답 보기</summary>

```lean
example (p q : Prop) (hq : q) : p ∨ q := by
  right
  exact hq

-- 또는 한 줄로:
-- exact Or.inr hq
```

**설명**:
- `right` 전술은 "p ∨ q를 증명하기 위해 q를 증명하겠다"는 선언이다

</details>

>  `cases`의 상세 설명은 **3편 3.11~3.12절** 참조. 여기서는 `| inl` / `| inr` 패턴만 기억하자.

### 연습 7: 논리합 분석 (cases)

```lean
-- 문제: p ∨ q이고, p → r이고, q → r이면, r이다
example (p q r : Prop) (h : p ∨ q) (hpr : p → r) (hqr : q → r) : r := by
  sorry  -- 빈칸을 채우시오
```

<details>
<summary>힌트 보기</summary>

`cases h with`을 사용하여 두 경우로 나눈다:
- 경우 1: `p`가 참인 경우
- 경우 2: `q`가 참인 경우

각 경우에서 해당 함축을 적용한다.

</details>

<details>
<summary>정답 보기</summary>

```lean
example (p q r : Prop) (h : p ∨ q) (hpr : p → r) (hqr : q → r) : r := by
  cases h with
  | inl hp =>
    exact hpr hp
  | inr hq =>
    exact hqr hq

-- 또는 rcases 사용:
-- rcases h with hp | hq
-- · exact hpr hp
-- · exact hqr hq

-- 또는 Or.elim 사용:
-- exact Or.elim h hpr hqr
```

**설명**:
- `cases h with`은 `p ∨ q`를 두 경우로 분리한다
- `| inl hp =>`는 "왼쪽(p)이 참인 경우"이고, `hp : p`가 주어진다
- `| inr hq =>`는 "오른쪽(q)이 참인 경우"이고, `hq : q`가 주어진다
- 각 경우에서 함축을 적용하여 `r`을 얻는다

</details>

### 연습 8: 논리합의 교환법칙

```lean
-- 문제: p ∨ q이면 q ∨ p임을 보여라
example (p q : Prop) (h : p ∨ q) : q ∨ p := by
  sorry  -- 빈칸을 채우시오
```

<details>
<summary>힌트 보기</summary>

두 경우로 나눈 후:
- p가 참이면 → q ∨ p의 오른쪽(p)을 증명
- q가 참이면 → q ∨ p의 왼쪽(q)을 증명

</details>

<details>
<summary>정답 보기</summary>

```lean
example (p q : Prop) (h : p ∨ q) : q ∨ p := by
  cases h with
  | inl hp =>
    right
    exact hp
  | inr hq =>
    left
    exact hq

-- 또는:
-- exact h.symm
-- 또는:
-- exact Or.comm.mp h
```

**설명**:
- p가 참이면: `q ∨ p`에서 오른쪽(p)을 선택 → `right` → `exact hp`
- q가 참이면: `q ∨ p`에서 왼쪽(q)을 선택 → `left` → `exact hq`

</details>

---

## 4-1.5 조건문 (Conditional/Implication): →

### 정의

명제 p와 q의 **조건문**(Conditional)은 "p이면 q이다"이며, **p → q**로 표기한다.
- p를 **가정**(hypothesis), **전제**(premise), **전건**(antecedent)이라 부른다
- q를 **결론**(conclusion), **결과**(consequence), **후건**(consequent)이라 부른다

### 진리표

| p | q | p → q |
|---|---|-------|
| T | T | T |
| T | F | F |
| F | T | T |
| F | F | T |

**핵심**: p → q는 **p가 참인데 q가 거짓**인 경우에만 거짓이다!

### 조건문의 다양한 표현

다음은 모두 p → q와 **같은 의미**이다:

| 표현 | 한국어 |
|------|--------|
| if p, then q | p이면 q이다 |
| p implies q | p는 q를 함축한다 |
| p only if q | p일 경우에만 q이다 |
| p is sufficient for q | p는 q의 충분조건이다 |
| q is necessary for p | q는 p의 필요조건이다 |
| q whenever p | p일 때마다 q이다 |
| q if p | p이면 q이다 |
| q unless ¬p | ¬p가 아니면 q이다 |

### Lean에서 조건문

```lean
-- p → q를 증명하려면: p를 가정하고 q를 보인다 (intro)
-- p → q를 사용하려면: p의 증거를 넣어서 q를 얻는다 (apply 또는 함수 적용)
```

>  `intro`, `apply`의 상세 설명은 **3편 3.8~3.10절** 참조

### 연습 9: 조건문 증명하기 (intro)

```lean
-- 문제: p → p를 증명하라 (항등 함축)
example (p : Prop) : p → p := by
  sorry  -- 빈칸을 채우시오
```

<details>
<summary>힌트 보기</summary>

`intro hp` 전술은 "p가 참이라고 가정하자"의 의미이다.
그러면 목표가 `p`로 바뀌고, `hp : p`가 가정에 추가된다.

</details>

<details>
<summary>정답 보기</summary>

```lean
example (p : Prop) : p → p := by
  intro hp
  exact hp

-- 또는 한 줄로:
-- exact fun hp => hp
-- 또는:
-- exact id
```

**설명**:
- `intro hp`: "p가 참이라 가정하자. 이를 hp라 부르자."
  - 가정에 `hp : p` 추가
  - 목표가 `p → p`에서 `p`로 변경
- `exact hp`: hp가 바로 p의 증거

</details>

### 연습 10: 조건문 사용하기 (apply)

```lean
-- 문제: p → q이고 p이면 q임을 보여라 (Modus Ponens)
example (p q : Prop) (hpq : p → q) (hp : p) : q := by
  sorry  -- 빈칸을 채우시오
```

<details>
<summary>힌트 보기</summary>

`hpq`는 함수처럼 동작한다. `hpq hp`는 p의 증거를 받아 q의 증거를 반환한다.
또는 `apply hpq`를 사용하여 목표를 p로 바꿀 수 있다.

</details>

<details>
<summary>정답 보기</summary>

```lean
example (p q : Prop) (hpq : p → q) (hp : p) : q := by
  apply hpq
  exact hp

-- 또는 한 줄로:
-- exact hpq hp
```

**설명**:
- `apply hpq`: "q를 증명하려면 p를 증명하면 된다" (hpq : p → q이므로)
- `exact hp`: p의 증거 제시

이것이 바로 **긍정 논법**(Modus Ponens)이다!

</details>

### 연습 11: 조건문의 합성 (삼단논법)

```lean
-- 문제: p → q이고 q → r이면 p → r임을 보여라 (가정적 삼단논법)
example (p q r : Prop) (hpq : p → q) (hqr : q → r) : p → r := by
  sorry  -- 빈칸을 채우시오
```

<details>
<summary>힌트 보기</summary>

1. 먼저 `intro hp`로 p를 가정한다
2. `hpq hp`로 q를 얻는다
3. `hqr (hpq hp)`로 r을 얻는다

</details>

<details>
<summary>정답 보기</summary>

```lean
example (p q r : Prop) (hpq : p → q) (hqr : q → r) : p → r := by
  intro hp
  apply hqr
  apply hpq
  exact hp

-- 또는 더 간단히:
-- intro hp
-- exact hqr (hpq hp)

-- 또는 한 줄로:
-- exact fun hp => hqr (hpq hp)
```

**설명**:
```
p → q → r 체인:
  hp : p
  hpq hp : q
  hqr (hpq hp) : r
```

</details>

---

## 4-1.6 역, 대우, 이 (Converse, Contrapositive, Inverse)

### 정의

조건문 p → q에서:

| 이름 | 기호 | 한국어 |
|------|------|--------|
| **원래 조건문** | p → q | p이면 q이다 |
| **역**(Converse) | q → p | q이면 p이다 |
| **대우**(Contrapositive) | ¬q → ¬p | q가 아니면 p가 아니다 |
| **이**(Inverse) | ¬p → ¬q | p가 아니면 q가 아니다 |

### 핵심 정리

- **p → q와 대우(¬q → ¬p)는 동치이다!** (항상 같은 진리값)
- p → q와 역(q → p)은 **동치가 아니다!**
- p → q와 이(¬p → ¬q)도 **동치가 아니다!**
- 역(q → p)과 이(¬p → ¬q)는 서로 **동치이다**

### 연습 12: 대우 증명

```lean
-- 문제: p → q이면 ¬q → ¬p임을 보여라
example (p q : Prop) (h : p → q) : ¬q → ¬p := by
  sorry  -- 빈칸을 채우시오
```

<details>
<summary>힌트 보기</summary>

1. `intro hnq`로 ¬q를 가정한다 (hnq : q → False)
2. `intro hp`로 p를 가정한다
3. `h hp`로 q를 얻는다
4. `hnq (h hp)`로 False를 얻는다 → 모순!

</details>

<details>
<summary>정답 보기</summary>

```lean
example (p q : Prop) (h : p → q) : ¬q → ¬p := by
  intro hnq
  intro hp
  apply hnq
  exact h hp

-- 또는:
-- intro hnq hp
-- exact hnq (h hp)

-- 또는 한 줄로:
-- exact fun hnq hp => hnq (h hp)
```

**설명**:
- `intro hnq`: ¬q를 가정 (hnq : q → False)
- `intro hp`: p를 가정
- `h hp`: p에서 q를 얻음
- `hnq (h hp)`: q에서 False를 얻음

이것이 **대우 증명법**(Proof by Contraposition)의 핵심이다!

</details>

---

## 4-1.7 상호 조건문 (Biconditional): ↔

### 정의

명제 p와 q의 **상호 조건문**(Biconditional)은 "p일 때 그리고 그때에만 q이다"이며, **p ↔ q**로 표기한다.

### 진리표

| p | q | p ↔ q |
|---|---|-------|
| T | T | T |
| T | F | F |
| F | T | F |
| F | F | T |

**핵심**: p ↔ q는 **p와 q의 진리값이 같을 때** 참이다.

### 상호 조건문의 다양한 표현

| 표현 | 한국어 |
|------|--------|
| p if and only if q | p일 때 그리고 그때에만 q |
| p iff q | p iff q |
| p is necessary and sufficient for q | p는 q의 필요충분조건이다 |
| p exactly when q | 정확히 p일 때 q이다 |

### 상호 조건문 = 양방향 조건문

**p ↔ q는 (p → q) ∧ (q → p)와 동치이다!**

### Lean에서 상호 조건문

```lean
-- p ↔ q를 증명하려면: 양방향을 각각 증명
-- p ↔ q를 사용하려면:
--   h.mp : p → q (정방향, modus ponens)
--   h.mpr : q → p (역방향, modus ponens reverse)
```

### 연습 13: 상호 조건문 증명

```lean
-- 문제: p ↔ p를 증명하라 (반사성)
example (p : Prop) : p ↔ p := by
  sorry  -- 빈칸을 채우시오
```

<details>
<summary>힌트 보기</summary>

`constructor`를 사용하여 두 방향을 각각 증명하거나,
`Iff.intro`를 사용하거나,
`Iff.rfl`을 사용할 수 있다.

</details>

<details>
<summary>정답 보기</summary>

```lean
example (p : Prop) : p ↔ p := by
  constructor
  · intro hp; exact hp
  · intro hp; exact hp

-- 또는:
-- exact Iff.rfl

-- 또는:
-- exact ⟨fun hp => hp, fun hp => hp⟩
```

**설명**:
- `constructor`는 `↔`를 두 개의 `→`로 분리한다
- 각 방향은 항등 함수 (받은 것 그대로 반환)

</details>

### 연습 14: 상호 조건문의 교환법칙

```lean
-- 문제: p ↔ q이면 q ↔ p임을 보여라
example (p q : Prop) (h : p ↔ q) : q ↔ p := by
  sorry  -- 빈칸을 채우시오
```

<details>
<summary>힌트 보기</summary>

`h.mp`와 `h.mpr`을 순서를 바꿔서 사용한다.
또는 `h.symm`을 사용할 수 있다.

</details>

<details>
<summary>정답 보기</summary>

```lean
example (p q : Prop) (h : p ↔ q) : q ↔ p := by
  constructor
  · exact h.mpr
  · exact h.mp

-- 또는 한 줄로:
-- exact h.symm

-- 또는:
-- exact ⟨h.mpr, h.mp⟩
```

**설명**:
- `h.mp : p → q` (정방향)
- `h.mpr : q → p` (역방향)
- 순서를 바꿔서 `⟨h.mpr, h.mp⟩`로 `q ↔ p`를 구성

</details>

### 연습 15: 상호 조건문 사용하기

```lean
-- 문제: p ↔ q이고 p이면 q임을 보여라
example (p q : Prop) (h : p ↔ q) (hp : p) : q := by
  sorry  -- 빈칸을 채우시오
```

<details>
<summary>힌트 보기</summary>

`h.mp`는 `p → q` 방향이다. 이것에 `hp`를 적용한다.

</details>

<details>
<summary>정답 보기</summary>

```lean
example (p q : Prop) (h : p ↔ q) (hp : p) : q := by
  exact h.mp hp

-- 또는:
-- rw [h] at hp
-- exact hp

-- 또는:
-- exact h.1 hp
```

**설명**:
- `h.mp`는 `p → q` 방향
- `h.mp hp`로 `q`를 얻는다

</details>

---

## 4-1.8 진리표를 Bool로 계산하기

### 계산 레일: Bool 사용

Lean에서 `Bool`은 `true`와 `false` 두 값을 가진다.
진리표를 **계산**으로 확인할 때 Bool을 사용한다.

```lean
-- Bool 연산
#eval !true           -- false (부정)
#eval true && false   -- false (논리곱)
#eval true || false   -- true (논리합)
```

### 조건문을 Bool로 정의

```lean
-- p → q는 ¬p ∨ q와 동치
def impB (p q : Bool) : Bool := !p || q

#eval impB true true    -- true
#eval impB true false   -- false
#eval impB false true   -- true
#eval impB false false  -- true
```

### 진리표 전체 출력

```lean
def allB : List Bool := [false, true]

def tableImp : List (Bool × Bool × Bool) :=
  allB.bind fun p => allB.map fun q => (p, q, impB p q)

#eval tableImp
-- [(false, false, true), (false, true, true), 
--  (true, false, false), (true, true, true)]
```

### 연습 16: 상호 조건문 Bool 정의

```lean
-- 문제: p ↔ q를 Bool로 정의하라
-- p ↔ q는 p와 q의 진리값이 같을 때 참이다
def iffB (p q : Bool) : Bool := sorry

-- 테스트
#eval iffB true true    -- 예상: true
#eval iffB true false   -- 예상: false
#eval iffB false true   -- 예상: false
#eval iffB false false  -- 예상: true
```

<details>
<summary>힌트 보기</summary>

p ↔ q는 (p → q) ∧ (q → p)와 동치이다.
또는 p == q로 직접 비교할 수도 있다.

</details>

<details>
<summary>정답 보기</summary>

```lean
def iffB (p q : Bool) : Bool := (impB p q) && (impB q p)

-- 또는 더 간단히:
-- def iffB (p q : Bool) : Bool := p == q
```

**설명**:
- `impB p q`는 `p → q`
- `impB q p`는 `q → p`
- 둘의 논리곱이 `p ↔ q`

</details>

---

## 4-1.9 복합 명제의 진리표

### 예제: (p ∨ ¬q) → (p ∧ q)의 진리표

| p | q | ¬q | p ∨ ¬q | p ∧ q | (p ∨ ¬q) → (p ∧ q) |
|---|---|-----|--------|-------|---------------------|
| T | T | F | T | T | T |
| T | F | T | T | F | F |
| F | T | F | F | F | T |
| F | F | T | T | F | F |

### Lean으로 계산

```lean
def example1 (p q : Bool) : Bool := impB (p || !q) (p && q)

#eval example1 true true    -- true
#eval example1 true false   -- false
#eval example1 false true   -- true
#eval example1 false false  -- false
```

### 연습 17: 복합 명제 계산

```lean
-- 문제: (p → q) ↔ (¬p ∨ q)의 진리표를 계산하라
-- 이 명제는 항상 참인가?

def exercise17 (p q : Bool) : Bool := iffB (impB p q) (!p || q)

#eval exercise17 true true    -- ?
#eval exercise17 true false   -- ?
#eval exercise17 false true   -- ?
#eval exercise17 false false  -- ?
```

<details>
<summary>정답 보기</summary>

```lean
#eval exercise17 true true    -- true
#eval exercise17 true false   -- true
#eval exercise17 false true   -- true
#eval exercise17 false false  -- true
```

**결론**: (p → q) ↔ (¬p ∨ q)는 **항진명제**(Tautology)이다!
모든 진리값 조합에서 참이다.

</details>

---

## 4-1.10 핵심 정리: (p → q) ↔ (¬p ∨ q)

### 이 동치가 왜 중요한가?

조건문 p → q를 논리합으로 변환할 수 있다:
- **p → q = ¬p ∨ q**

이를 통해 조건문 증명을 논리합 증명으로 바꿀 수 있다!

### 연습 18: 핵심 동치 증명

```lean
-- 문제: (p → q) ↔ (¬p ∨ q)를 증명하라
-- 이것은 0장 과제의 핵심!

example (p q : Prop) : (p → q) ↔ (¬p ∨ q) := by
  sorry  -- 빈칸을 채우시오
```

<details>
<summary>힌트 보기</summary>

**→ 방향 (p → q) → (¬p ∨ q):**
- 고전 논리에서 **배중률**(Law of Excluded Middle)을 사용해야 한다
- `Classical.em p`는 `p ∨ ¬p`를 제공한다
- p가 참인 경우: `h hp`로 q를 얻어 `Or.inr`
- p가 거짓인 경우: `Or.inl`

**← 방향 (¬p ∨ q) → (p → q):**
- ¬p ∨ q를 경우 분석
- ¬p인 경우: p가 주어지면 모순
- q인 경우: 직접 q 반환

</details>

<details>
<summary>정답 보기</summary>

```lean
example (p q : Prop) : (p → q) ↔ (¬p ∨ q) := by
  constructor
  -- (→) 방향: (p → q) → (¬p ∨ q)
  · intro h
    by_cases hp : p
    · -- p가 참인 경우
      right
      exact h hp
    · -- p가 거짓인 경우
      left
      exact hp
  -- (←) 방향: (¬p ∨ q) → (p → q)
  · intro h
    intro hp
    cases h with
    | inl hnp =>
      -- ¬p인 경우, p가 주어지면 모순
      exfalso
      exact hnp hp
    | inr hq =>
      -- q인 경우
      exact hq
```

**설명**:
- `by_cases hp : p`는 고전 논리의 **배중률**을 사용한다
- p ∨ ¬p 중 어느 쪽인지 경우를 나눈다
- `exfalso`는 목표를 `False`로 바꾼다 (모순 증명)

</details>

---

## 4-1.11 배타적 논리합 (Exclusive Or): ⊕

### 정의

명제 p와 q의 **배타적 논리합**(Exclusive Or)은 p ⊕ q로 표기한다.
"p 또는 q 중 **정확히 하나**"의 의미이다.

### 진리표

| p | q | p ⊕ q |
|---|---|-------|
| T | T | F |
| T | F | T |
| F | T | T |
| F | F | F |

**핵심**: p ⊕ q는 p와 q의 진리값이 **다를 때** 참이다.

### 배타적 논리합 = 다름

**p ⊕ q = (p ∨ q) ∧ ¬(p ∧ q)**
또는
**p ⊕ q = (p ∧ ¬q) ∨ (¬p ∧ q)**

### Lean에서 배타적 논리합

```lean
-- Lean의 Xor 정의
#check Xor'

-- Bool에서
#eval xor true true    -- false
#eval xor true false   -- true
#eval xor false true   -- true
#eval xor false false  -- false
```

### 연습 19: 배타적 논리합 증명

```lean
-- 문제: p ⊕ q이면 p ∨ q임을 보여라
example (p q : Prop) (h : Xor' p q) : p ∨ q := by
  sorry  -- 빈칸을 채우시오
```

<details>
<summary>힌트 보기</summary>

`Xor' p q`는 `(p ∧ ¬q) ∨ (¬p ∧ q)`와 같다.
경우를 나누어 각각에서 p 또는 q를 꺼낸다.

</details>

<details>
<summary>정답 보기</summary>

```lean
example (p q : Prop) (h : Xor' p q) : p ∨ q := by
  cases h with
  | inl hpnq =>
    left
    exact hpnq.left
  | inr hnpq =>
    right
    exact hnpq.right
```

**설명**:
- `Xor' p q`는 `(p ∧ ¬q) ∨ (¬p ∧ q)`
- 왼쪽 경우: `p ∧ ¬q`에서 p를 꺼냄
- 오른쪽 경우: `¬p ∧ q`에서 q를 꺼냄

</details>

---

## 4-1.12 논리 연산자 우선순위

### 연산자 우선순위 (높은 것부터)

| 순위 | 연산자 | 이름 |
|------|--------|------|
| 1 | ¬ | 부정 |
| 2 | ∧ | 논리곱 |
| 3 | ∨ | 논리합 |
| 4 | → | 조건문 |
| 5 | ↔ | 상호조건문 |

### 예시

```
¬p ∧ q    =  (¬p) ∧ q        (부정이 먼저)
p ∧ q ∨ r =  (p ∧ q) ∨ r    (논리곱이 먼저)
p ∨ q → r =  (p ∨ q) → r    (논리합이 먼저)
p → q ↔ r =  (p → q) ↔ r    (조건문이 먼저)
```

### 연습 20: 우선순위 적용

```lean
-- 문제: ¬p ∨ q → p ∧ r 에서 괄호를 명시적으로 넣으면?

-- 정답: ((¬p) ∨ q) → (p ∧ r)

-- 이를 증명해보자
example (p q r : Prop) : (¬p ∨ q → p ∧ r) = ((¬p ∨ q) → (p ∧ r)) := by
  rfl
```

---

## 4-1.13 Rosen 1장 연습문제 Lean 변환

### 문제 10 (p.16)

p: "I bought a lottery ticket this week."
q: "I won the million dollar jackpot."

다음 명제들을 영어로 표현하라.

```lean
-- 이 문제는 Lean 증명이 아니라 이해를 위한 것
-- Lean에서 표현만 해보자

variable (p q : Prop)  -- p: 복권 구매, q: 잭팟 당첨

#check ¬p           -- (a) "I did not buy a lottery ticket this week."
#check p ∨ q        -- (b) "I bought a lottery ticket this week or I won the jackpot."
#check p → q        -- (c) "If I bought a lottery ticket this week, I won the jackpot."
#check p ∧ q        -- (d) "I bought a lottery ticket and won the jackpot."
#check p ↔ q        -- (e) "I bought a lottery ticket iff I won the jackpot."
#check ¬p → ¬q      -- (f) "If I didn't buy a ticket, I didn't win."
#check ¬p ∨ (p ∧ q) -- (g) "I didn't buy a ticket or I bought and won."
```

### 문제 18 (p.17): 상호조건문 판정

다음 상호조건문이 참인지 거짓인지 판정하라.

```lean
-- (a) 2 + 2 = 4 if and only if 1 + 1 = 2
example : (2 + 2 = 4) ↔ (1 + 1 = 2) := by
  constructor <;> intro _ <;> rfl

-- (b) 1 + 1 = 2 if and only if 2 + 3 = 4
-- 1 + 1 = 2는 참, 2 + 3 = 4는 거짓이므로 전체는 거짓
-- Lean에서는 거짓인 명제를 증명할 수 없음

-- (c) 1 + 1 = 3 if and only if monkeys can fly
-- 둘 다 거짓이므로 전체는 참!
-- (단, "monkeys can fly"를 거짓인 명제로 정의해야 함)
```

### 문제 19 (p.17): 조건문 참/거짓

```lean
-- (a) If 1 + 1 = 2, then 2 + 2 = 5
-- 가정 참, 결론 거짓 → 전체 거짓
-- Lean에서는 이걸 증명할 수 없음 (실제로 거짓이니까)

-- (b) If 1 + 1 = 3, then 2 + 2 = 4
-- 가정 거짓 → 전체 참! (공허한 참)
example : (1 + 1 = 3) → (2 + 2 = 4) := by
  intro h
  rfl  -- 결론이 참이므로 바로 증명됨

-- (c) If 1 + 1 = 3, then 2 + 2 = 5
-- 가정 거짓 → 전체 참! (공허한 참)
example : (1 + 1 = 3) → (2 + 2 = 5) := by
  intro h
  -- h : 1 + 1 = 3 인데, 이건 거짓
  -- 거짓에서는 무엇이든 증명 가능 (False.elim)
  norm_num at h  -- h에서 모순 발견
```

### 문제 29 (p.18): 역, 대우, 이

"If it snows today, I will ski tomorrow."의 역, 대우, 이를 구하라.

```lean
-- 원문: p → q
-- p = "It snows today"
-- q = "I will ski tomorrow"

variable (p q : Prop)

-- 역 (Converse): q → p
-- "If I ski tomorrow, then it snowed today."
#check (q → p : Prop)

-- 대우 (Contrapositive): ¬q → ¬p
-- "If I don't ski tomorrow, then it didn't snow today."
#check (¬q → ¬p : Prop)

-- 이 (Inverse): ¬p → ¬q
-- "If it doesn't snow today, I won't ski tomorrow."
#check (¬p → ¬q : Prop)
```

---

## 4-1.14 종합 연습 문제

### 연습 21: 드모르간 법칙 1

```lean
-- 문제: ¬(p ∨ q) ↔ (¬p ∧ ¬q)를 증명하라
example (p q : Prop) : ¬(p ∨ q) ↔ (¬p ∧ ¬q) := by
  sorry  -- 빈칸을 채우시오
```

<details>
<summary>힌트 보기</summary>

**→ 방향**: 
- `¬(p ∨ q)`가 있으면, p가 참일 경우 `Or.inl`로 `p ∨ q`가 되어 모순
- q도 마찬가지

**← 방향**:
- `¬p ∧ ¬q`가 있고 `p ∨ q`를 가정하면, 경우 분석으로 모순 도출

</details>

<details>
<summary>정답 보기</summary>

```lean
example (p q : Prop) : ¬(p ∨ q) ↔ (¬p ∧ ¬q) := by
  constructor
  -- (→) 방향
  · intro h
    constructor
    · intro hp
      apply h
      left
      exact hp
    · intro hq
      apply h
      right
      exact hq
  -- (←) 방향
  · intro h
    intro hpq
    cases hpq with
    | inl hp => exact h.left hp
    | inr hq => exact h.right hq
```

**설명**: 이것이 **드모르간 법칙**(De Morgan's Law) 중 하나이다!

</details>

### 연습 22: 드모르간 법칙 2

```lean
-- 문제: ¬(p ∧ q) ↔ (¬p ∨ ¬q)를 증명하라
-- 이 방향은 고전 논리가 필요하다!

example (p q : Prop) : ¬(p ∧ q) ↔ (¬p ∨ ¬q) := by
  sorry  -- 빈칸을 채우시오
```

<details>
<summary>힌트 보기</summary>

**→ 방향**에서 `by_cases`(배중률)를 사용해야 한다.
**← 방향**은 직관주의 논리로도 가능하다.

</details>

<details>
<summary>정답 보기</summary>

```lean
example (p q : Prop) : ¬(p ∧ q) ↔ (¬p ∨ ¬q) := by
  constructor
  -- (→) 방향: 고전 논리 필요
  · intro h
    by_cases hp : p
    · -- p가 참인 경우
      right
      intro hq
      apply h
      exact ⟨hp, hq⟩
    · -- p가 거짓인 경우
      left
      exact hp
  -- (←) 방향
  · intro h
    intro hpq
    cases h with
    | inl hnp => exact hnp hpq.left
    | inr hnq => exact hnq hpq.right
```

**설명**: 이것이 **드모르간 법칙**의 두 번째 형태이다.

</details>

### 연습 23: 분배법칙

```lean
-- 문제: p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r)를 증명하라
example (p q r : Prop) : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := by
  sorry  -- 빈칸을 채우시오
```

<details>
<summary>정답 보기</summary>

```lean
example (p q r : Prop) : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := by
  constructor
  -- (→) 방향
  · intro h
    cases h.right with
    | inl hq =>
      left
      exact ⟨h.left, hq⟩
    | inr hr =>
      right
      exact ⟨h.left, hr⟩
  -- (←) 방향
  · intro h
    cases h with
    | inl hpq =>
      exact ⟨hpq.left, Or.inl hpq.right⟩
    | inr hpr =>
      exact ⟨hpr.left, Or.inr hpr.right⟩
```

**설명**: 논리곱이 논리합에 대해 **분배**된다.

</details>

### 연습 24: 흡수법칙

```lean
-- 문제: p ∨ (p ∧ q) ↔ p를 증명하라
example (p q : Prop) : p ∨ (p ∧ q) ↔ p := by
  sorry  -- 빈칸을 채우시오
```

<details>
<summary>정답 보기</summary>

```lean
example (p q : Prop) : p ∨ (p ∧ q) ↔ p := by
  constructor
  -- (→) 방향
  · intro h
    cases h with
    | inl hp => exact hp
    | inr hpq => exact hpq.left
  -- (←) 방향
  · intro hp
    left
    exact hp
```

**설명**: 이것이 **흡수법칙**(Absorption Law)이다.

</details>

---

## 4-1.15 전술 요약표

### 이 장에서 사용한 전술들

| 전술 | 용도 | 예시 |
|------|------|------|
| `intro h` | 가정 도입 (→, ∀) | `intro hp`로 `p` 가정 |
| `exact h` | 정확히 일치하는 증거 제시 | `exact hp` |
| `apply h` | 목표를 h의 조건으로 변경 | `apply hpq`로 목표 `q`→`p` |
| `constructor` | ∧, ↔ 분해 | 두 개의 하위 목표 생성 |
| `left` | ∨의 왼쪽 선택 | `p ∨ q`에서 `p` 증명 |
| `right` | ∨의 오른쪽 선택 | `p ∨ q`에서 `q` 증명 |
| `cases h with` | 경우 분석 (∨, ∃) | 두 경우로 나눔 |
| `by_cases h : p` | 배중률 (고전 논리) | `p ∨ ¬p`로 분기 |
| `exfalso` | 모순 증명으로 전환 | 목표를 `False`로 변경 |
| `rfl` | 반사성 (정의상 같음) | `a = a` |

### 유용한 정리들

| 정리 | 타입 | 설명 |
|------|------|------|
| `And.intro` | `p → q → p ∧ q` | 논리곱 구성 |
| `And.left` | `p ∧ q → p` | 왼쪽 추출 |
| `And.right` | `p ∧ q → q` | 오른쪽 추출 |
| `Or.inl` | `p → p ∨ q` | 왼쪽으로 논리합 |
| `Or.inr` | `q → p ∨ q` | 오른쪽으로 논리합 |
| `Or.elim` | `p ∨ q → (p → r) → (q → r) → r` | 논리합 제거 |
| `Iff.intro` | `(p → q) → (q → p) → p ↔ q` | 상호조건문 구성 |
| `Iff.mp` | `p ↔ q → p → q` | 정방향 |
| `Iff.mpr` | `p ↔ q → q → p` | 역방향 |
| `Classical.em` | `p ∨ ¬p` | 배중률 |



---

## 4-1.17 참고: Lean 입력 방법

### 논리 기호 입력

| 기호 | 입력 방법 | 이름 |
|------|----------|------|
| ¬ | `\not` 또는 `\neg` | 부정 |
| ∧ | `\and` 또는 `\wedge` | 논리곱 |
| ∨ | `\or` 또는 `\vee` | 논리합 |
| → | `\to` 또는 `\r` | 조건문 |
| ↔ | `\iff` 또는 `\lr` | 상호조건문 |
| ⟨ | `\langle` 또는 `\<` | 왼쪽 꺾쇠 |
| ⟩ | `\rangle` 또는 `\>` | 오른쪽 꺾쇠 |
| ← | `\l` 또는 `\leftarrow` | 왼쪽 화살표 |

---

