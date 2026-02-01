# Lean 4 핵심 레퍼런스

> 이산수학 × 형식 검증 통합 교과과정  
> 택틱(Tactic), 타입 시스템, 증명 방법론

---

## 제1부: Lean 4 기초 - 타입 시스템

### 1.1 변수와 타입 선언

Lean 4에서 모든 변수는 반드시 타입을 가져야 한다. `variable` 키워드로 변수를 선언하고, `#check` 명령어로 표현식의 타입을 검사할 수 있다.

```lean
-- 변수 선언
variable (n : Nat)        -- n은 자연수 타입
variable (x : Int)        -- x는 정수 타입
variable (s : String)     -- s는 문자열 타입

-- 타입 검사
#check n + 0              -- 결과: Nat
#check "Hello"            -- 결과: String
#check (10 : Int)         -- 10을 정수로 명시
```

**핵심 개념:**

Lean의 타입 시스템은 `Prop`(명제)과 `Type`(데이터)을 명확히 구분한다. `Prop`은 논리적 주장을 나타내고, `Type`은 계산 가능한 값을 나타낸다.

### 1.2 집합과 서술어 (Set as Predicate)

Lean에서 집합 `Set α`는 실제로 `α → Prop` 타입의 함수, 즉 서술어(Predicate)로 정의된다. 원소 `x`가 집합 `S`에 속한다는 것은 함수 `S`에 `x`를 적용했을 때 참인 명제가 반환된다는 의미이다.

```lean
-- 짝수 집합 정의
def Evens : Set Nat := {n | n % 2 == 0}

-- 이는 다음과 동일
def Evens' (n : Nat) : Prop := n % 2 == 0
```

이러한 접근은 집합을 '특성 함수(Characteristic Function)'로 바라보는 함수형 프로그래밍의 관점과 일치한다.

### 1.3 함수 정의

Lean 4에서 함수는 일급 시민(First-class Citizen)으로서, 다른 함수의 인자가 되거나 반환값이 될 수 있다.

```lean
-- def 키워드로 함수 정의
def square (x : Nat) : Nat := x * x

-- fun 키워드로 익명 함수 (Lambda Expression)
def add_one := fun x => x + 1

-- 평가
#eval square 5        -- 결과: 25
#eval add_one 10      -- 결과: 11
```

---

## 제2부: 논리 연산자 - 명제로서의 타입

### 2.1 논리 연산자와 귀납적 타입

전통적인 논리학에서 ∧(그리고), ∨(또는), ¬(부정), →(함의)는 진리값을 조작하는 연산자이다. Lean 4에서 이들은 데이터 구조체로 정의된다.

| 논리 연산자 | 수학적 의미 | Lean 4 타입 | 프로그래머 비유 |
|------------|-----------|-------------|---------------|
| `P ∧ Q` | P 그리고 Q | `structure And P Q` | Pair/Tuple |
| `P ∨ Q` | P 또는 Q | `inductive Or P Q` | Enum/Union |
| `P → Q` | P이면 Q | `P -> Q` | 함수 |
| `¬P` | P가 아니다 | `P -> False` | 모순 도출 함수 |
| `P ↔ Q` | P와 Q는 동치 | `structure Iff P Q` | 양방향 함수 쌍 |

### 2.2 커리-하워드 대응 (Proofs as Programs)

'명제는 타입이며, 증명은 프로그램이다' - 이것이 커리-하워드 동형성의 핵심이다.

**전건 긍정식(Modus Ponens)은 함수 적용이다:**

함수 `f : P -> Q`와 값 `p : P`가 있을 때, `f p`는 `Q` 타입의 값을 반환한다. 즉, `P → Q`와 `P`가 참이면 `Q`도 참이라는 논리적 규칙은 함수에 인자를 넣어 결과값을 얻는 것과 동일하다.

```lean
-- 삼단논법을 함수 합성으로 구현
def syllogism (f : P -> Q) (g : Q -> R) : P -> R :=
  fun x => g (f x)

-- 전건 긍정식
example (h1 : P) (h2 : P → Q) : Q := h2 h1
```

---

## 제3부: 택틱(Tactic) - 자동화된 추론

### 3.1 택틱 모드 기본

직접적인 증명항(Proof Term) 작성은 복잡할 수 있다. Lean 4는 이를 보조하기 위해 명령형 언어 스타일의 '택틱(Tactic)'을 제공한다.

```lean
-- by 키워드로 택틱 모드 진입
example (P Q : Prop) : P → Q → P ∧ Q := by
  intro hP      -- P를 가정으로 추가
  intro hQ      -- Q를 가정으로 추가
  constructor   -- ∧를 두 하위 목표로 분리
  exact hP      -- 첫 번째 목표: hP 사용
  exact hQ      -- 두 번째 목표: hQ 사용
```

### 3.2 핵심 택틱 상세 설명

#### intro: 가정 도입

함의 도입(→-introduction) 규칙에 해당한다. 목표가 `P → Q`일 때, 전제 `P`를 컨텍스트로 이동시킨다.

```lean
example : P → P := by
  intro h    -- h : P를 가정에 추가, 목표는 P
  exact h    -- h가 정확히 목표
```

#### apply: 후방 연쇄 추론

함의 제거(→-elimination) 규칙이다. 결론 `Q`를 증명하기 위해 `P → Q` 함수를 적용하면, 새로운 목표는 `P`를 증명하는 것으로 바뀐다.

```lean
example (h : P → Q) (hp : P) : Q := by
  apply h    -- 목표가 Q에서 P로 변경
  exact hp   -- P의 증거 제공
```

#### exact: 정확한 증거 제공

목표 타입과 정확히 일치하는 항을 제공하여 증명을 종료한다.

#### rw (Rewrite): 치환

등식 `a = b`를 이용하여 명제 내의 `a`를 `b`로(혹은 그 반대로) 치환한다.

```lean
-- rw 사용 예시
example (h : a = b) : a + 1 = b + 1 := by
  rw [h]     -- a를 b로 치환, 목표: b + 1 = b + 1
             -- 자동으로 rfl 적용되어 완료

-- 역방향 치환
example (h : a = b) : b + 1 = a + 1 := by
  rw [← h]   -- b를 a로 치환
```

#### constructor: 구조 분해

목표가 ∧(And) 또는 ↔(Iff) 형태일 때, 두 개의 하위 목표로 분리한다.

```lean
example (hP : P) (hQ : Q) : P ∧ Q := by
  constructor   -- 두 목표로 분리
  · exact hP    -- 첫 번째: P
  · exact hQ    -- 두 번째: Q
```

#### cases: 경우 분석

Or 가정이나 귀납적 타입을 분해하여 각 경우를 처리한다.

```lean
example (h : P ∨ Q) : Q ∨ P := by
  cases h with
  | inl hp => right; exact hp   -- P인 경우
  | inr hq => left; exact hq    -- Q인 경우
```

---

## 제4부: 한정자(Quantifiers) - 의존 타입

### 4.1 전칭 한정자 (∀) - 의존 함수 타입

'모든 x ∈ D에 대하여 P(x)이다'는 의존 함수 타입(Pi Type)으로 구현된다. 표기법은 `(x : α) → P x` 또는 `∀ x, P x`이다.

```lean
-- 전칭 한정자 증명
example : ∀ n : Nat, n = n := by
  intro n    -- 임의의 n을 고정
  rfl        -- 반사성으로 증명

-- 함수 표현
def all_eq_self : ∀ n : Nat, n = n := 
  fun n => rfl
```

`intro` 택틱을 사용하여 임의의 원소를 가정하고, `specialize` 택틱을 사용하여 일반적인 정리를 특정 값에 적용할 수 있다.

### 4.2 존재 한정자 (∃) - 의존 쌍 타입

'D에 속하는 어떤 x에 대하여 P(x)이다'는 의존 쌍 타입(Sigma Type)으로 모델링된다. 구조체 `Exists P`는 증인(Witness) `w`와 그 증인이 성질을 만족한다는 증명 `h : P(w)`의 쌍이다.

```lean
-- 존재성 증명: use로 증인 제시
example : ∃ x : Nat, x > 10 := by
  use 100        -- 100이 증인
  simp           -- 100 > 10 자동 증명

-- 존재 가정 분해: rcases 또는 obtain
example (h : ∃ x, P x) : ... := by
  rcases h with ⟨x, hx⟩   -- x와 hx : P x 추출
  -- 또는
  obtain ⟨x, hx⟩ := h
```

**주의: Exists vs Sigma**

알고리즘 내에서 값을 추출해 사용하려면 `Sigma`를, 단순한 존재성 증명만 필요하다면 `Exists`를 사용한다.

### 4.3 한정자 부정: push_neg

`push_neg` 택틱은 복잡한 논리식의 부정을 자동으로 계산한다.

```lean
-- ¬∀x.P(x) ↔ ∃x.¬P(x)
-- ¬∃x.P(x) ↔ ∀x.¬P(x)

example : ¬(∀ x, P x) ↔ ∃ x, ¬P x := by
  push_neg
  rfl
```

---

## 제5부: 증명 방법론

### 5.1 직접 증명 (Direct Proof)

`calc` 블록을 사용하여 등식의 변형 과정을 단계별로 기술한다.

```lean
-- calc 블록 예시
example (a b c : Nat) (h1 : a = b) (h2 : b = c) : a = c := by
  calc a = b := h1
       _ = c := h2

-- ring 택틱으로 대수적 항등식 자동 증명
example : (a + b)^2 = a^2 + 2*a*b + b^2 := by
  ring
```

### 5.2 간접 증명: 대우와 귀류법

#### 대우 증명 (contrapose)

`P → Q`를 증명하기 위해 `¬Q → ¬P`를 증명한다.

```lean
example : P → Q := by
  contrapose     -- 목표가 ¬Q → ¬P로 변경
  intro hnq
  -- ¬P 증명...
```

#### 귀류법 (by_contra)

목표의 부정을 가정(`h : ¬P`)하고 모순(`False`)을 이끌어낸다.

```lean
example : P := by
  by_contra h    -- h : ¬P 가정
  -- False 도출...

-- 고전 논리 사용 (배중률)
open Classical in
example : P ∨ ¬P := em P
```

Lean은 기본적으로 구성적 논리(Constructive Logic)를 따르므로, 귀류법을 사용하려면 `Classical` 네임스페이스가 필요할 수 있다.

### 5.3 귀납법 (Induction)

자연수 `Nat`은 `zero`와 `succ` 생성자를 가진 귀납적 타입이다. `induction` 택틱으로 기저 사례와 귀납 단계로 분할한다.

```lean
-- 수학적 귀납법
example (P : Nat → Prop) (h0 : P 0) (hs : ∀ n, P n → P (n+1)) : 
    ∀ n, P n := by
  intro n
  induction n with
  | zero => exact h0                    -- 기저 사례
  | succ k ih => exact hs k ih          -- 귀납 단계 (ih: 귀납 가설)
```

구조적 귀납법은 `List`, `BinaryTree` 등 재귀적으로 정의된 구조에도 적용된다.

---

## 제6부: 택틱 빠른 참조표

| 택틱 | 사용 상황 | 효과 |
|-----|----------|------|
| `rfl` | 양변이 계산상 동일 | 반사성으로 자동 증명 |
| `intro h` | 목표가 ∀ 또는 → 형태 | 변수/가정을 컨텍스트로 이동 |
| `apply h` | h : A → B이고 목표가 B | 목표를 A로 변경 (후방 연쇄) |
| `exact h` | h가 정확히 목표와 일치 | 증명 완료 |
| `rw [h]` | h : a = b 등식 있을 때 | 목표의 a를 b로 치환 |
| `rw [← h]` | 역방향 치환 필요 | 목표의 b를 a로 치환 |
| `constructor` | 목표가 ∧ 또는 ↔ | 두 하위 목표로 분리 |
| `cases h` | h : A ∨ B 또는 귀납적 타입 | 각 경우로 분리 |
| `rcases h with ⟨x,hx⟩` | h : ∃ x, P x | 증인 x와 성질 hx 추출 |
| `use x` | 목표가 ∃ x, P x | 증인 x 제시, 목표는 P x |
| `induction n` | n이 귀납적 타입 | 기저/귀납 단계로 분리 |
| `contrapose` | 목표가 P → Q | 목표를 ¬Q → ¬P로 변경 |
| `by_contra h` | 귀류법 사용 | ¬(목표)를 가정, False 도출 |
| `push_neg` | 복잡한 부정식 | 부정을 내부로 밀어넣음 |
| `simp` | 간단한 계산/단순화 | 자동 단순화 규칙 적용 |
| `ring` | 대수적 항등식 | 환(ring) 구조 자동 증명 |
| `linarith` | 일차 부등식/등식 | 선형 산술 자동 증명 |
| `sorry` | 임시로 증명 생략 | 나중에 채울 자리 표시 |

---

## 기호 입력 방법

| 기호 | 입력 방법 | 의미 |
|-----|----------|------|
| `→` | `\to` 또는 `\r` 또는 `->` | 함의 (이면) |
| `↔` | `\iff` 또는 `\lr` | 동치 (iff) |
| `∀` | `\forall` | 전칭 한정자 |
| `∃` | `\exists` | 존재 한정자 |
| `∧` | `\and` 또는 `/\` | 논리곱 (And) |
| `∨` | `\or` 또는 `\/` | 논리합 (Or) |
| `¬` | `\not` 또는 `\neg` | 부정 (Not) |
| `←` | `\l` 또는 `\leftarrow` | 역방향 화살표 (rw용) |
| `⟨ ⟩` | `\<` `\>` 또는 `\langle` `\rangle` | 꺾쇠 괄호 (구조분해) |
| `·` | `\.` 또는 `\cdot` | 하위 목표 구분 점 |

---

*— 끝 —*
