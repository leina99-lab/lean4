# Lean 4 튜토리얼 — 제1편: 명제 논리 기초

> **이 편의 목표**: 명제(Prop)가 무엇인지, 증명이 무엇인지, 그리고 Lean 4에서 전술(tactic)로 증명을 한 단계씩 쌓아가는 방법을 익힌다.
>
> **선행 학습**: 제0편 (def, theorem, rfl, #check, #eval, Type vs Prop)
>
> **이 편에서 배우는 전술**: `by`, `intro`, `exact`, `apply`

---

## 1.1 명제(Prop)란 무엇인가?

### 명제 = 참 또는 거짓인 문장

**명제**(Proposition)는 "참이거나 거짓인 주장"이다.

```
명제인 것:
  "2 + 2 = 4"             → 참인 명제
  "1 = 2"                 → 거짓인 명제
  "모든 짝수는 2로 나누어진다" → 참인 명제
  "5는 짝수다"             → 거짓인 명제

명제가 아닌 것:
  "안녕하세요"             → 인사 (참/거짓 없음)
  "밥 먹었니?"             → 질문 (참/거짓 없음)
  "문을 닫아라"            → 명령 (참/거짓 없음)
```

### Lean 4에서 Prop 타입

```lean
#check 2 + 2 = 4       -- 2 + 2 = 4 : Prop
#check 1 = 2           -- 1 = 2 : Prop
#check 3 < 5           -- 3 < 5 : Prop
```

**결과 읽는 법:**
```
2 + 2 = 4 : Prop
    ↑         ↑
    │         └── 이것의 타입은 Prop(명제)다
    └── 이 표현식은
```

### 핵심: 거짓인 명제도 Prop이다

```lean
#check 1 = 2           -- 1 = 2 : Prop
```

`1 = 2`는 **거짓**이지만 **명제이다.** "명제인가"와 "참인가"는 별개의 문제다.

```
"지구는 평평하다" → 거짓이지만, 명제는 맞다
"2 + 2 = 5"      → 거짓이지만, 명제는 맞다

명제인지 아닌지  ≠  참인지 거짓인지
```

---

## 1.2 Bool과 Prop의 차이 (심화)

제0편에서 Type의 세계와 Prop의 세계를 간략히 살펴봤다. 여기서는 특히 **Bool과 Prop**의 차이를 정확히 짚는다.

| 구분 | **Bool** | **Prop** |
|------|----------|----------|
| 세계 | Type의 세계 (데이터) | Prop의 세계 (논리) |
| 가능한 값 | `true`, `false` 딱 2개 | **증명**(proof) — 무한히 다양 |
| 확인 방법 | `#eval`로 계산 | `theorem`으로 증명 |
| 목적 | 프로그램 실행 | 논리적 추론 |

### 예시로 비교

```lean
-- Bool: 계산해서 true/false를 얻는다
#eval 2 < 3          -- true
#eval 5 == 5         -- true
#eval 10 < 5         -- false
```

```lean
-- Prop: 증명이 필요하다
#check (2 < 3 : Prop)      -- 2 < 3 : Prop  (명제만 확인)
-- #eval (2 < 3 : Prop)    -- 오류! Prop은 #eval 불가

-- 증명해야만 "참임"을 인정받는다
theorem two_lt_three : 2 < 3 := by decide
```

### 비유로 이해하기

```
Bool = 계산기
  버튼 누르면 즉시 답이 나온다
  "2 < 3이야?" → [계산] → "true!"

Prop = 법정
  판사가 판결을 내려야 한다
  "2 < 3이다" → [증명 제출] → "참으로 인정!"

계산기는 빠르지만 단순한 것만 처리 가능하다.
법정은 느리지만 복잡한 수학적 사실도 다룰 수 있다.
```

**왜 둘 다 필요한가?**

```lean
-- Bool은 프로그램 실행에 쓴다
def checkAge (age : Nat) : String :=
  if age >= 18 then "성인" else "미성년"

#eval checkAge 20    -- "성인"
#eval checkAge 15    -- "미성년"
```

```lean
-- Prop은 수학적 사실을 증명하는 데 쓴다
theorem all_add_zero (n : Nat) : n + 0 = n := by
  intro       -- (∀가 아니므로 생략, rfl로 충분)
  rfl
```

---

## 1.3 증명이란 무엇인가?

### 증명 = 명제의 "값"

Lean 4에서 **증명도 값이다.** 이것이 Lean 4의 가장 중요한 설계 원리다.

```
일반 프로그래밍:
  타입 : Nat
  값   : 42

Lean 4 증명:
  타입 : 2 + 2 = 4    (명제가 타입!)
  값   : rfl           (증명이 값!)
```

### 코드로 비교

```lean
-- 일반 값 정의
def myNumber : Nat := 42
--     ↑         ↑     ↑
--     이름       타입  값

-- 증명
theorem myProof : 2 + 2 = 4 := rfl
--       ↑              ↑      ↑
--       이름            명제   증명(값)
```

구조가 완전히 같다. 이름 `:` 타입 `:=` 값. 단지 타입이 `Nat` 대신 `2 + 2 = 4`(명제)이고, 값이 `42` 대신 `rfl`(증명)일 뿐이다.

### 커리-하워드 대응(Curry-Howard Correspondence)

"명제 = 타입, 증명 = 값"이라는 대응 관계를 **커리-하워드 대응**이라고 한다.

```
논리학               ↔    프로그래밍
───────────────────────────────────
명제                ↔    타입
증명                ↔    값
P → Q (함의)        ↔    함수 타입 (P를 받아 Q를 돌려주는 함수)
P ∧ Q (논리 곱)     ↔    곱타입 (P와 Q를 묶은 쌍)
P ∨ Q (논리 합)     ↔    합타입 (P 또는 Q 중 하나)
```

이 대응 덕분에 Lean 4는 프로그래밍 언어이면서 동시에 증명 시스템이 될 수 있다. 제2편 이후에서 각 대응을 하나씩 직접 확인하게 된다.

---

## 1.4 전술 모드(Tactic Mode)와 by

### 두 가지 증명 방식

Lean 4에서 증명을 작성하는 방식은 두 가지다.

#### (1) 항 모드(Term Mode) — 증명 값을 직접 적는다

```lean
theorem ex_term : 2 + 2 = 4 := rfl
--                             ↑
--                             증명 값을 직접 적음
```

#### (2) 전술 모드(Tactic Mode) — 단계별로 증명한다

```lean
theorem ex_tactic : 2 + 2 = 4 := by
  rfl
--                               ↑
--                               by 이후 전술을 사용
```

### by가 하는 일

`by`는 "지금부터 전술 모드로 증명하겠다"는 선언이다.

```lean
theorem 이름 : 명제 := by
  -- 여기서부터 전술 모드
  -- 전술 1
  -- 전술 2
  -- ...
  -- 모든 목표가 해결되면 증명 완료
```

### 전술(Tactic)이란?

**전술**은 증명을 한 단계씩 진행하는 명령어다.

```
비유: 요리 레시피

  "파스타 만들기"
  1단계: 물을 끓인다   (전술 1)
  2단계: 면을 넣는다   (전술 2)
  3단계: 8분 기다린다  (전술 3)
  4단계: 소스를 넣는다 (전술 4)
  완성!
```

증명도 마찬가지다. 각 전술이 현재의 "증명 상태"를 바꾸면서 목표를 향해 나아간다.

### 항 모드 vs 전술 모드

```lean
-- 간단한 증명: 항 모드면 충분하다
theorem simple : 2 + 2 = 4 := rfl

-- 복잡한 증명: 전술 모드가 필요하다
-- (이 예제는 제2편에서 완전히 이해하게 된다)
theorem and_comm (P Q : Prop) : P ∧ Q → Q ∧ P := by
  intro h
  obtain ⟨hp, hq⟩ := h
  exact ⟨hq, hp⟩
```

---

## 1.5 증명 상태(Goal State) 읽는 법

### VS Code에서 보이는 것

전술 모드에서 커서를 움직이면 오른쪽 **Lean Infoview** 패널에 증명 상태가 표시된다.

```
1 goal
P Q : Prop
h : P ∧ Q
⊢ Q ∧ P
```

### 읽는 법

```
1 goal         ← 남은 목표의 개수
P Q : Prop     ← 컨텍스트: 선언된 변수
h : P ∧ Q      ← 컨텍스트: 사용 가능한 가정(hypothesis)
⊢ Q ∧ P        ← 지금 증명해야 할 목표(goal)
```

**⊢ 기호**: "턴스타일(turnstile)"이라고 읽는다. "이것을 증명해야 한다"는 의미다. Dict의 A-3 항목에 자세한 설명이 있다.

### 전술이 상태를 바꾼다

각 전술을 적용하면 증명 상태가 변한다. 이 변화를 추적하는 것이 Lean 4 증명의 핵심이다.

아래는 `P → Q → P`를 증명하는 예제다. 각 전술 전후의 상태를 모두 보여준다.

```lean
example (P Q : Prop) : P → Q → P := by
  -- [초기 상태]
  -- ⊢ P → Q → P

  intro hp
  -- [intro hp 후]
  -- hp : P
  -- ⊢ Q → P

  intro hq
  -- [intro hq 후]
  -- hp : P
  -- hq : Q
  -- ⊢ P

  exact hp
  -- [exact hp 후]
  -- 목표 없음 (증명 완료)
```

**규칙**: 목표가 `P → ...` 형태이면 `intro`로 가정을 가져온다. 목표가 가정과 정확히 일치하면 `exact`로 완료한다. 이 두 규칙만 알아도 많은 증명을 할 수 있다.

---

## 1.6 핵심 전술 1: intro

### intro가 하는 일

`intro`는 "가정을 도입한다"는 전술이다.

목표가 `P → Q` 형태일 때, `intro hp`는 "P가 참이라고 가정하고, 이 가정을 `hp`라고 부르겠다"는 의미다. 그 후 목표는 `Q`로 바뀐다.

### 언제 쓰는가?

```
목표가 이런 형태일 때:
  P → Q        → intro 사용 (가정 도입)
  ∀ x, P x     → intro 사용 (임의의 원소 도입)
```

### 수학 증명 ↔ Lean 4 1:1 대응

**명제: P → Q → P**

| 수학적 증명 | Lean 4 전술 |
|-----------|------------|
| P가 참이라고 가정하자. | `intro hp` |
| Q가 참이라고 가정하자. | `intro hq` |
| P는 첫 번째 가정 hp에 의해 참이다. | `exact hp` |

```lean
-- 수학 증명:
-- 가정: P, Q
-- 보일 것: P
-- 증명: P는 가정에 의해 참. □

example (P Q : Prop) : P → Q → P := by
  intro hp    -- P가 참이라고 가정, hp라고 부름
  intro hq    -- Q가 참이라고 가정, hq라고 부름
  exact hp    -- P는 hp이므로 참
```

**InfoView 변화 확인:**

```
[시작]
⊢ P → Q → P

[intro hp 후]
hp : P
⊢ Q → P

[intro hq 후]
hp : P
hq : Q
⊢ P

[exact hp 후]
증명 완료
```

### 두 개를 한 번에 도입하기

```lean
example (P Q : Prop) : P → Q → P := by
  intro hp hq    -- 두 가정을 한 번에 도입
  exact hp
```

### ∀(전칭 양화사)에도 사용한다

```lean
-- 수학 증명:
-- 임의의 자연수 n을 잡는다.
-- n = n은 자명하다. □

example : ∀ n : Nat, n = n := by
  intro n      -- 임의의 자연수 n을 잡음
  rfl          -- n = n은 자명 (반사성)
```

```
[시작]
⊢ ∀ n : Nat, n = n

[intro n 후]
n : Nat
⊢ n = n

[rfl 후]
증명 완료
```

**핵심**: `∀ n`을 증명하려면 "아무 n이나 하나 잡아서 성립함을 보이면 된다." `intro n`이 바로 그 작업이다.

---

## 1.7 핵심 전술 2: exact

### exact가 하는 일

`exact`는 "정확히 이것이 증명이다"라고 말하는 전술이다.

현재 목표와 타입이 **정확히 일치하는** 항(term)을 제시하면 그 목표가 완료된다.

### 언제 쓰는가?

```
목표와 정확히 일치하는 가정이나 항이 이미 있을 때 사용
```

### 수학 증명 ↔ Lean 4 1:1 대응

**명제: 가정 h : P가 있으면 P이다**

| 수학적 증명 | Lean 4 전술 |
|-----------|------------|
| h는 P의 증명이므로 P가 성립한다. | `exact h` |

```lean
example (P : Prop) (h : P) : P := by
  -- [시작]
  -- h : P
  -- ⊢ P

  exact h
  -- "h가 바로 P의 증명이다"
  -- 증명 완료
```

### exact의 조건: 타입이 정확히 일치해야 한다

```lean
example (P : Prop) (h : P) : P := by
  exact h      -- ✓ h의 타입이 P, 목표도 P

-- 이건 안 된다:
-- example (P Q : Prop) (h : P) : Q := by
--   exact h    -- ✗ h의 타입은 P, 목표는 Q (불일치)
```

### 함수처럼 적용하기

`h : P → Q`이고 `hp : P`가 있으면, `h hp`의 타입은 `Q`다. 함수 적용과 동일하다.

```lean
example (P Q : Prop) (h : P → Q) (hp : P) : Q := by
  -- h : P → Q
  -- hp : P
  -- ⊢ Q

  exact h hp
  -- h는 "P를 받아서 Q를 주는 함수"
  -- h hp : Q  (h에 hp를 넣어서 Q를 얻음)
```

**커리-하워드 대응 재확인:**

```
h : P → Q  =  "P의 증명을 받으면 Q의 증명을 돌려주는 함수"
hp : P     =  "P의 증명"
h hp : Q   =  "h라는 함수에 hp를 넣어 얻은 Q의 증명"
```

---

## 1.8 핵심 전술 3: apply

### apply가 하는 일

`apply`는 "이 정리/가정을 현재 목표에 적용하겠다"는 전술이다.

`exact`와의 차이:
- **exact**: 목표를 **완성**한다 (목표와 정확히 일치하는 것을 제시)
- **apply**: 목표를 **더 작은 목표로 바꾼다** (결론에서 가정으로 거슬러 올라감)

### 작동 원리

`h : A → B`를 현재 목표 `B`에 `apply h`하면, 목표가 `A`로 바뀐다.

"B를 증명하려면 A를 증명하면 된다 (h를 통해 A → B이므로)."

### 수학 증명 ↔ Lean 4 1:1 대응

**명제: P → Q이고 Q → R이면 P → R이다 (삼단논법)**

수학적 증명:
```
P가 참이라고 가정하자.
hpq: P → Q이므로, P로부터 Q를 얻는다.
hqr: Q → R이므로, Q로부터 R을 얻는다.
따라서 R이 성립한다. □
```

Lean 4 증명:

```lean
theorem modus_ponens_chain
    (P Q R : Prop)
    (hpq : P → Q) (hqr : Q → R) (hp : P) : R := by
  -- [시작]
  -- hpq : P → Q
  -- hqr : Q → R
  -- hp  : P
  -- ⊢ R

  apply hqr
  -- "R을 증명하려면 Q를 증명하면 된다 (hqr : Q → R)"
  -- [apply hqr 후]
  -- ⊢ Q

  apply hpq
  -- "Q를 증명하려면 P를 증명하면 된다 (hpq : P → Q)"
  -- [apply hpq 후]
  -- ⊢ P

  exact hp
  -- hp : P가 목표와 일치
  -- 증명 완료
```

**수학 증명 단계와 Lean 전술의 1:1 대응:**

| 수학적 증명 | Lean 4 전술 |
|-----------|------------|
| P가 참이라고 가정하자 (가정 hp). | (이미 hp가 있음) |
| hqr 적용: Q이면 R을 얻는다. | `apply hqr` (목표: Q) |
| hpq 적용: P이면 Q를 얻는다. | `apply hpq` (목표: P) |
| P는 hp에 의해 성립한다. | `exact hp` |

### 흐름 시각화

```
┌─────────────────────────────────┐
│ 목표: R                         │
│ 가정: hqr : Q → R               │
└─────────────────────────────────┘
              │
              │ apply hqr
              │ "R을 얻으려면 Q가 필요하다"
              ▼
┌─────────────────────────────────┐
│ 목표: Q                         │
│ 가정: hpq : P → Q               │
└─────────────────────────────────┘
              │
              │ apply hpq
              │ "Q를 얻으려면 P가 필요하다"
              ▼
┌─────────────────────────────────┐
│ 목표: P                         │
│ 가정: hp : P                    │
└─────────────────────────────────┘
              │
              │ exact hp
              ▼
         증명 완료
```

### 짧게 쓰기

위 증명은 `exact`만으로도 쓸 수 있다.

```lean
-- 전술 모드
theorem modus_ponens_chain' (P Q R : Prop)
    (hpq : P → Q) (hqr : Q → R) (hp : P) : R := by
  exact hqr (hpq hp)

-- 항 모드
theorem modus_ponens_chain'' (P Q R : Prop)
    (hpq : P → Q) (hqr : Q → R) (hp : P) : R :=
  hqr (hpq hp)
```

둘 다 같은 증명이다. 전술 모드는 단계적으로 생각할 때, 항 모드는 흐름이 보일 때 쓴다.

---

## 1.9 전술 요약

이 편에서 배운 전술 세 가지를 정리한다.

| 전술 | 목표 형태 | 하는 일 |
|------|----------|--------|
| `intro x` | `P → Q` 또는 `∀ x, P x` | 가정/변수를 도입하고 목표를 축소 |
| `exact e` | 목표와 `e`의 타입이 일치 | 증명 완료 |
| `apply h` | `h : A → B`, 목표가 `B` | 목표를 `A`로 변경 |

**자주 쓰는 패턴:**

```lean
-- 패턴 1: intro → exact
example (P : Prop) : P → P := by
  intro h
  exact h

-- 패턴 2: intro → apply → exact
example (P Q R : Prop) (f : P → Q) (g : Q → R) : P → R := by
  intro hp
  apply g
  exact f hp

-- 패턴 3: intro → apply → apply → exact (삼단논법 연쇄)
example (P Q R S : Prop) (f : P → Q) (g : Q → R) (h : R → S) : P → S := by
  intro hp
  apply h
  apply g
  exact f hp
```

---

## 1.10 연습 문제

### 1단계: 빈칸 채우기

다음 증명의 빈칸에 알맞은 전술을 채워라.

**문제 1-1**

```lean
-- "P이면 P이다"
example (P : Prop) : P → P := by
  _____ hp
  exact hp
```

<details>
<summary>정답 보기</summary>

```lean
example (P : Prop) : P → P := by
  intro hp
  exact hp
```
</details>

---

**문제 1-2**

```lean
-- "P → Q이고 P이면 Q이다" (전건 긍정, Modus Ponens)
example (P Q : Prop) (h : P → Q) (hp : P) : Q := by
  _____ h
  _____ hp
```

<details>
<summary>정답 보기</summary>

```lean
example (P Q : Prop) (h : P → Q) (hp : P) : Q := by
  apply h
  exact hp
-- 또는:
-- exact h hp
```
</details>

---

**문제 1-3**

```lean
-- "모든 자연수 n에 대해 n + 0 = n이다"
example : ∀ n : Nat, n + 0 = n := by
  _____ n
  _____
```

<details>
<summary>정답 보기</summary>

```lean
example : ∀ n : Nat, n + 0 = n := by
  intro n
  rfl
```
</details>

---

### 2단계: sorry 완성하기

`sorry`를 실제 전술로 교체하여 증명을 완성하라.

**문제 2-1**

```lean
-- "P이고 Q이면 Q이고 P이다"
-- 힌트: intro h로 가정을 받은 후,
--       h.1과 h.2로 P와 Q를 각각 꺼낼 수 있다 (제2편에서 자세히 배운다)
--       지금은 exact h.right로 Q를, exact h.left로 P를 쓴다
example (P Q : Prop) (h : P ∧ Q) : Q := by
  sorry
```

<details>
<summary>정답 보기</summary>

```lean
example (P Q : Prop) (h : P ∧ Q) : Q := by
  exact h.right
-- 또는:
-- exact h.2
```
</details>

---

**문제 2-2**

```lean
-- "P → Q → R이고 P이고 Q이면 R이다"
theorem ex2_2 (P Q R : Prop) (h : P → Q → R) (hp : P) (hq : Q) : R := by
  sorry
```

<details>
<summary>정답 보기</summary>

```lean
theorem ex2_2 (P Q R : Prop) (h : P → Q → R) (hp : P) (hq : Q) : R := by
  apply h
  · exact hp
  · exact hq
-- 또는:
-- exact h hp hq
```
</details>

---

**문제 2-3**

```lean
-- "P → Q이고 Q → R이고 R → S이면 P → S이다"
theorem ex2_3 (P Q R S : Prop)
    (hpq : P → Q) (hqr : Q → R) (hrs : R → S) : P → S := by
  sorry
```

<details>
<summary>정답 보기</summary>

```lean
theorem ex2_3 (P Q R S : Prop)
    (hpq : P → Q) (hqr : Q → R) (hrs : R → S) : P → S := by
  intro hp
  apply hrs
  apply hqr
  exact hpq hp
```
</details>

---

### 3단계: 자유 증명

힌트 없이 처음부터 증명을 작성하라.

**문제 3-1**

```lean
-- "모든 명제 P에 대해 P → P → P이다"
-- (같은 가정이 두 번 나와도 된다)
theorem ex3_1 (P : Prop) : P → P → P := by
  sorry
```

<details>
<summary>정답 보기</summary>

```lean
theorem ex3_1 (P : Prop) : P → P → P := by
  intro hp _    -- 두 번째 가정은 사용하지 않으므로 _로 받음
  exact hp
```
</details>

---

**문제 3-2**

```lean
-- "∀ m n : Nat, m = n → n = m"
-- 힌트: Eq.symm을 알면 exact Eq.symm h로 한 줄에 끝난다.
--       apply와 intro만 써서도 증명해보라.
theorem ex3_2 : ∀ m n : Nat, m = n → n = m := by
  sorry
```

<details>
<summary>정답 보기</summary>

```lean
theorem ex3_2 : ∀ m n : Nat, m = n → n = m := by
  intro m n h
  exact h.symm
-- 또는:
-- exact Eq.symm h
```
</details>

---

**문제 3-3: 도전 문제**

```lean
-- "(P → Q → R) ↔ (P ∧ Q → R)"  (카레 동형, Currying)
-- 힌트: ↔는 제3편에서 자세히 다룬다.
--       constructor로 양방향을 각각 증명한다.
theorem currying (P Q R : Prop) : (P → Q → R) ↔ (P ∧ Q → R) := by
  sorry
```

<details>
<summary>정답 보기</summary>

```lean
theorem currying (P Q R : Prop) : (P → Q → R) ↔ (P ∧ Q → R) := by
  constructor
  · intro h hpq
    exact h hpq.1 hpq.2
  · intro h hp hq
    exact h ⟨hp, hq⟩
```
</details>

---

## 1.11 이 편의 핵심 요약

### 핵심 개념

**명제(Prop)**: 참 또는 거짓인 주장. 거짓인 명제도 Prop이다.

**Bool vs Prop**: Bool은 계산으로 `true`/`false`를 얻는다. Prop은 `theorem`으로 증명해야 한다.

**증명 = 값**: Lean 4에서 증명은 명제를 타입으로 갖는 값이다. 이것이 커리-하워드 대응이다.

**전술 모드**: `by` 이후 전술을 나열하여 단계적으로 증명한다. VS Code의 Lean Infoview에서 각 단계의 상태를 확인한다.

### 배운 전술

```
intro x    : 목표가 P → Q 또는 ∀ x, P x 일 때
             가정/변수를 도입하고 목표를 축소한다.

exact e    : e의 타입이 목표와 정확히 일치할 때
             증명을 완료한다.

apply h    : h : A → B이고 목표가 B일 때
             목표를 A로 변경한다.
```

### 다음 편 예고

**제2편: 논리 연산자**에서는 ∧(그리고), ∨(또는), ¬(아니다), →(이면)의 수학적 정의와 진리표를 다루고, 각각을 Lean 4에서 증명하는 방법을 배운다.

새로 배울 전술: `constructor`, `obtain`, `left`, `right`, `rcases`
