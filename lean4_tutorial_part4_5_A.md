# Lean4 완전 정복 가이드 — 제4-5편 (Part A)

## 증명 방법과 전략 완전 정복

> **교재**: Kenneth H. Rosen, "Discrete Mathematics and Its Applications" 8판  
> **범위**: 1.8절 증명 방법과 전략  
> **선수 학습**: 제4-4편(추론 규칙과 증명의 소개)

---

## 4-5.0 이 장의 목표

이 장에서는 다음을 학습한다:

1. **전수 증명**(Exhaustive Proof)과 **경우에 의한 증명**(Proof by Cases)의 원리
2. **일반성을 잃지 않고**(Without Loss of Generality, WLOG)의 의미와 활용
3. **존재 증명**(Existence Proof): **생산적**(Constructive)과 **비생산적**(Nonconstructive) 방법
4. **유일성 증명**(Uniqueness Proof)의 구조
5. **전향 추론**(Forward Reasoning)과 **후향 추론**(Backward Reasoning)
6. **반례**(Counterexample) 찾기
7. Lean4에서 이 모든 것을 어떻게 구현하는지

---

## 4-5.1 전수 증명과 경우에 의한 증명의 기초

### 4-5.1.1 전수 증명이란?

**전수 증명**(exhaustive proof)이란 **모든 가능한 경우를 빠짐없이 조사**하여 정리를 증명하는 방법이다.

**언제 사용하는가?**
- 가능한 경우의 수가 **비교적 적을 때**
- 각 경우를 **개별적으로 검증할 수 있을 때**
- **유한한 집합**에 대한 명제를 다룰 때

**일상 예시**:
> "우리 가족 모두가 아이스크림을 좋아한다"를 증명하려면?
> - 아빠가 아이스크림을 좋아한다 ✓
> - 엄마가 아이스크림을 좋아한다 ✓
> - 나도 아이스크림을 좋아한다 ✓
> - 동생도 아이스크림을 좋아한다 ✓
> 
> 가족 구성원 **모두**를 검사했으므로 증명 완료!

### 4-5.1.2 경우에 의한 증명의 추론 규칙

**경우에 의한 증명**(proof by cases)은 다음 추론 규칙에 기반한다:

$$[(p_1 \vee p_2 \vee \cdots \vee p_n) \rightarrow q] \leftrightarrow [(p_1 \rightarrow q) \wedge (p_2 \rightarrow q) \wedge \cdots \wedge (p_n \rightarrow q)]$$

**이것이 무슨 뜻인가?**

| 왼쪽 | 오른쪽 |
|------|--------|
| "p₁ 또는 p₂ 또는 ... 또는 pₙ이면 q이다" | "p₁이면 q이고, p₂이면 q이고, ..., pₙ이면 q이다" |

**핵심 아이디어**: 여러 경우 중 **하나가 반드시 성립**하고, **각 경우에서 결론이 따라나온다면**, 그 결론은 참이다!

### 4-5.1.3 왜 이 규칙이 성립하는가?

진리표로 확인해 보자. 간단히 n = 2인 경우를 보면:

| p₁ | p₂ | q | p₁ ∨ p₂ | (p₁ ∨ p₂) → q | p₁ → q | p₂ → q | (p₁ → q) ∧ (p₂ → q) |
|----|----|----|---------|---------------|--------|--------|---------------------|
| T | T | T | T | T | T | T | T |
| T | T | F | T | F | F | F | F |
| T | F | T | T | T | T | T | T |
| T | F | F | T | F | F | T | F |
| F | T | T | T | T | T | T | T |
| F | T | F | T | F | T | F | F |
| F | F | T | F | T | T | T | T |
| F | F | F | F | T | T | T | T |

5번째 열과 8번째 열이 **항상 같다**! 따라서 논리적 동치이다.

### 4-5.1.4 전수 증명 vs 경우에 의한 증명

| 구분 | 전수 증명 | 경우에 의한 증명 |
|------|---------|--------------|
| **범위** | 모든 경우를 직접 검사 | 경우를 분류하여 각각 증명 |
| **경우의 수** | 보통 적음 (유한하고 작음) | 적거나 많을 수 있음 |
| **특징** | 각 경우를 개별 확인 | 각 경우마다 별도의 증명 필요 |
| **관계** | 경우에 의한 증명의 특수한 형태 | 더 일반적인 방법 |
| **예시** | "1~4의 정수에 대해..." | "정수가 양수, 0, 음수인 경우..." |

---

## 4-5.2 교재 예제: 전수 증명 (예제 1)

### 4-5.2.1 문제

> **예제 1** (Rosen 1.8절):  
> n이 n ≤ 4인 양의 정수이면 (n + 1)³ ≥ 3n임을 증명하라.

### 4-5.2.2 풀이 전략

n ≤ 4인 양의 정수는 n = 1, 2, 3, 4 **오직 네 가지**뿐이다.

각 경우를 **개별적으로 검사**하면 된다!

### 4-5.2.3 상세 풀이

**경우 1**: n = 1일 때
$$\text{좌변} = (1+1)^3 = 2^3 = 8$$
$$\text{우변} = 3 \times 1 = 3$$
$$8 \geq 3 \quad \checkmark$$

**경우 2**: n = 2일 때
$$\text{좌변} = (2+1)^3 = 3^3 = 27$$
$$\text{우변} = 3 \times 2 = 6$$
$$27 \geq 6 \quad \checkmark$$

**경우 3**: n = 3일 때
$$\text{좌변} = (3+1)^3 = 4^3 = 64$$
$$\text{우변} = 3 \times 3 = 9$$
$$64 \geq 9 \quad \checkmark$$

**경우 4**: n = 4일 때
$$\text{좌변} = (4+1)^3 = 5^3 = 125$$
$$\text{우변} = 3 \times 4 = 12$$
$$125 \geq 12 \quad \checkmark$$

### 4-5.2.4 결과 정리표

| n | (n+1)³ 계산 | 3n 계산 | (n+1)³ ≥ 3n 확인 |
|---|-------------|---------|------------------|
| 1 | 2³ = 8 | 3 | 8 ≥ 3 ✓ |
| 2 | 3³ = 27 | 6 | 27 ≥ 6 ✓ |
| 3 | 4³ = 64 | 9 | 64 ≥ 9 ✓ |
| 4 | 5³ = 125 | 12 | 125 ≥ 12 ✓ |

**결론**: 네 가지 경우 **모두**에서 부등식이 성립하므로, 정리가 증명되었다!

### 4-5.2.5 왜 이것이 정당한 증명인가?

논리 구조를 명확히 하자:

1. **증명하려는 명제**: ∀n ∈ {1, 2, 3, 4}, (n+1)³ ≥ 3n

2. **경우 분류**: n ∈ {1, 2, 3, 4}이면 (n = 1) ∨ (n = 2) ∨ (n = 3) ∨ (n = 4)

3. **각 경우 증명**:
   - (n = 1) → ((n+1)³ ≥ 3n) ✓
   - (n = 2) → ((n+1)³ ≥ 3n) ✓
   - (n = 3) → ((n+1)³ ≥ 3n) ✓
   - (n = 4) → ((n+1)³ ≥ 3n) ✓

4. **경우에 의한 증명 규칙 적용**: 모든 경우에서 결론이 성립하므로 원래 명제 참!

---

## 4-5.3 Lean4에서 전수 증명 구현하기

### 4-5.3.1 Lean4의 결정 가능성 개념

Lean4에서 어떤 명제가 **결정 가능**(Decidable)하다는 것은, 그 명제의 참/거짓을 **알고리즘적으로 판정**할 수 있다는 뜻이다.

```lean
-- Decidable 타입 클래스 (참고용)
#check @Decidable     -- Prop → Type
#check @decide        -- (p : Prop) → [Decidable p] → Bool

-- 간단한 예: 2 < 5는 결정 가능
#eval decide (2 < 5)   -- true
#eval decide (5 < 2)   -- false
```

**왜 중요한가?**

전수 증명은 "모든 경우를 검사"하는 것이다. Lean4에서 명제가 결정 가능하면, 컴퓨터가 **자동으로** 모든 경우를 검사할 수 있다!

### 4-5.3.2 `decide`와 `native_decide` 전술

| 전술 | 설명 | 장점 | 단점 |
|-----|------|-----|------|
| `decide` | Lean 내부에서 계산 | 증명 항이 작음 | 느릴 수 있음 |
| `native_decide` | 네이티브 코드로 컴파일 | 빠름 | 증명 항이 큼 |

```lean
-- decide 사용: 작은 계산에 적합
example : 2 + 2 = 4 := by decide
example : (3 : Nat) < 5 := by decide

-- native_decide 사용: 큰 계산에 적합
example : 100 * 100 = 10000 := by native_decide
example : (125 : Nat) ≥ 12 := by native_decide
```

### 4-5.3.3 예제 1의 각 경우를 Lean4로

```lean
-- 예제 1: n ≤ 4인 양의 정수에 대해 (n+1)³ ≥ 3n

-- n = 1인 경우
example : (1 + 1)^3 ≥ 3 * 1 := by native_decide
-- Lean이 계산: 2³ = 8, 3 × 1 = 3, 8 ≥ 3? true!

-- n = 2인 경우
example : (2 + 1)^3 ≥ 3 * 2 := by native_decide
-- Lean이 계산: 3³ = 27, 3 × 2 = 6, 27 ≥ 6? true!

-- n = 3인 경우
example : (3 + 1)^3 ≥ 3 * 3 := by native_decide
-- Lean이 계산: 4³ = 64, 3 × 3 = 9, 64 ≥ 9? true!

-- n = 4인 경우
example : (4 + 1)^3 ≥ 3 * 4 := by native_decide
-- Lean이 계산: 5³ = 125, 3 × 4 = 12, 125 ≥ 12? true!
```

### 4-5.3.4 #eval로 계산 확인하기

Lean4의 `#eval` 명령어로 계산 결과를 직접 확인할 수 있다:

```lean
-- 각 경우의 좌변과 우변 계산
#eval (1 + 1)^3    -- 결과: 8
#eval 3 * 1        -- 결과: 3

#eval (2 + 1)^3    -- 결과: 27
#eval 3 * 2        -- 결과: 6

#eval (3 + 1)^3    -- 결과: 64
#eval 3 * 3        -- 결과: 9

#eval (4 + 1)^3    -- 결과: 125
#eval 3 * 4        -- 결과: 12
```

### 4-5.3.5 Fin 타입: 유한 범위 표현

Lean4의 `Fin n` 타입은 **0부터 n-1까지**의 자연수를 나타낸다.

```lean
-- Fin 5는 {0, 1, 2, 3, 4}를 나타냄
#check (0 : Fin 5)   -- Fin 5 타입
#check (1 : Fin 5)   -- Fin 5 타입
#check (4 : Fin 5)   -- Fin 5 타입
-- #check (5 : Fin 5)   -- 오류! 5는 Fin 5의 범위를 벗어남

-- Fin n의 값을 Nat으로 변환: Fin.val
#check Fin.val       -- Fin n → Nat

example : (3 : Fin 5).val = 3 := rfl
example : (0 : Fin 5).val = 0 := rfl
```

**왜 Fin을 사용하는가?**

`Fin n`은 **정확히 n개**의 원소를 가지므로, Lean4가 **모든 경우를 자동으로 열거**할 수 있다!

### 4-5.3.6 Fin을 사용한 전수 증명 자동화

```lean
-- "1 ≤ n ≤ 4인 모든 n에 대해 (n+1)³ ≥ 3n"
-- Fin 5는 {0, 1, 2, 3, 4}를 포함
-- n ≠ 0인 경우만 고려하면 {1, 2, 3, 4}

example : ∀ n : Fin 5, n.val ≠ 0 → (n.val + 1)^3 ≥ 3 * n.val := by
  decide   -- Lean이 모든 경우를 자동으로 검사!
```

**이것이 어떻게 작동하는가?**

1. Lean은 `Fin 5`의 **모든 원소**(0, 1, 2, 3, 4)를 열거
2. 각 원소 n에 대해 `n.val ≠ 0 → (n.val + 1)^3 ≥ 3 * n.val`을 검사
3. n = 0인 경우: 전제 `0 ≠ 0`이 **거짓**이므로 조건문은 자동으로 참 (공허한 참)
4. n = 1, 2, 3, 4인 경우: 계산하여 부등식 확인
5. **모든 경우가 참**이므로 증명 완료!

### 4-5.3.7 전수 증명의 한계

**주의**: 전수 증명은 경우의 수가 **적을 때만** 실용적이다!

```lean
-- 이것은 작동한다 (경우가 5개)
example : ∀ n : Fin 5, n.val^2 < 25 := by decide

-- 이것은 매우 오래 걸리거나 실패할 수 있다 (경우가 1000개)
-- example : ∀ n : Fin 1000, n.val^2 < 1000000 := by decide
-- → 너무 많은 경우!
```

---

### 4-5.3.8 연습문제 1: 전수 증명 기초

#### 연습 1-1: 개별 검사
```lean
-- n = 1, 2, 3에 대해 n² + n이 짝수임을 개별적으로 검사하라
-- 힌트: 짝수는 2로 나누어떨어진다, 즉 n % 2 = 0

example : (1^2 + 1) % 2 = 0 := by sorry
example : (2^2 + 2) % 2 = 0 := by sorry
example : (3^2 + 3) % 2 = 0 := by sorry
```

<details>
<summary>💡 답 보기</summary>

```lean
example : (1^2 + 1) % 2 = 0 := by native_decide  -- 1 + 1 = 2, 2 % 2 = 0
example : (2^2 + 2) % 2 = 0 := by native_decide  -- 4 + 2 = 6, 6 % 2 = 0
example : (3^2 + 3) % 2 = 0 := by native_decide  -- 9 + 3 = 12, 12 % 2 = 0
```

**설명**:
- n² + n = n(n+1)은 **연속한 두 정수의 곱**이므로 항상 짝수!
- 연속한 두 정수 중 **적어도 하나**는 짝수이기 때문이다.
- n = 1: 1 × 2 = 2 (짝수)
- n = 2: 2 × 3 = 6 (짝수)
- n = 3: 3 × 4 = 12 (짝수)

</details>

#### 연습 1-2: 거듭제곱 부등식
```lean
-- n = 1, 2, 3, 4, 5에 대해 2^n > n임을 개별적으로 검사하라

example : (2 : Nat)^1 > 1 := by sorry
example : (2 : Nat)^2 > 2 := by sorry
example : (2 : Nat)^3 > 3 := by sorry
example : (2 : Nat)^4 > 4 := by sorry
example : (2 : Nat)^5 > 5 := by sorry
```

<details>
<summary>💡 답 보기</summary>

```lean
example : (2 : Nat)^1 > 1 := by native_decide  -- 2 > 1 ✓
example : (2 : Nat)^2 > 2 := by native_decide  -- 4 > 2 ✓
example : (2 : Nat)^3 > 3 := by native_decide  -- 8 > 3 ✓
example : (2 : Nat)^4 > 4 := by native_decide  -- 16 > 4 ✓
example : (2 : Nat)^5 > 5 := by native_decide  -- 32 > 5 ✓
```

**계산 확인표**:

| n | 2ⁿ | 2ⁿ > n? |
|---|-----|---------|
| 1 | 2 | 2 > 1 ✓ |
| 2 | 4 | 4 > 2 ✓ |
| 3 | 8 | 8 > 3 ✓ |
| 4 | 16 | 16 > 4 ✓ |
| 5 | 32 | 32 > 5 ✓ |

</details>

#### 연습 1-3: Fin을 사용한 자동 전수 증명
```lean
-- 1 ≤ n ≤ 3인 모든 n에 대해 n³ < 30임을 증명하라
-- 힌트: Fin 4를 사용하고, n.val ≠ 0 조건 추가

example : ∀ n : Fin 4, n.val ≠ 0 → n.val^3 < 30 := by
  sorry
```

<details>
<summary>💡 답 보기</summary>

```lean
example : ∀ n : Fin 4, n.val ≠ 0 → n.val^3 < 30 := by
  decide
```

**검증**:
- n = 0: 전제 `0 ≠ 0`이 거짓이므로 자동으로 참
- n = 1: 1³ = 1 < 30 ✓
- n = 2: 2³ = 8 < 30 ✓
- n = 3: 3³ = 27 < 30 ✓

</details>

#### 연습 1-4: 합의 성질
```lean
-- n = 0, 1, 2, 3에 대해 n + (n + 1) = 2*n + 1임을 검사하라

example : 0 + (0 + 1) = 2 * 0 + 1 := by sorry
example : 1 + (1 + 1) = 2 * 1 + 1 := by sorry
example : 2 + (2 + 1) = 2 * 2 + 1 := by sorry
example : 3 + (3 + 1) = 2 * 3 + 1 := by sorry
```

<details>
<summary>💡 답 보기</summary>

```lean
example : 0 + (0 + 1) = 2 * 0 + 1 := by native_decide  -- 0 + 1 = 1 = 0 + 1
example : 1 + (1 + 1) = 2 * 1 + 1 := by native_decide  -- 1 + 2 = 3 = 2 + 1
example : 2 + (2 + 1) = 2 * 2 + 1 := by native_decide  -- 2 + 3 = 5 = 4 + 1
example : 3 + (3 + 1) = 2 * 3 + 1 := by native_decide  -- 3 + 4 = 7 = 6 + 1
```

**일반화**: n + (n+1) = 2n + 1은 대수적으로 자명하다!

</details>

#### 연습 1-5: 제곱수 성질
```lean
-- n = 1, 2, 3, 4에 대해 (n+1)² - n² = 2n + 1임을 검사하라
-- 이것은 "연속한 제곱수의 차는 홀수"라는 성질이다

example : (1 + 1)^2 - 1^2 = 2 * 1 + 1 := by sorry
example : (2 + 1)^2 - 2^2 = 2 * 2 + 1 := by sorry
example : (3 + 1)^2 - 3^2 = 2 * 3 + 1 := by sorry
example : (4 + 1)^2 - 4^2 = 2 * 4 + 1 := by sorry
```

<details>
<summary>💡 답 보기</summary>

```lean
example : (1 + 1)^2 - 1^2 = 2 * 1 + 1 := by native_decide  -- 4 - 1 = 3 = 3
example : (2 + 1)^2 - 2^2 = 2 * 2 + 1 := by native_decide  -- 9 - 4 = 5 = 5
example : (3 + 1)^2 - 3^2 = 2 * 3 + 1 := by native_decide  -- 16 - 9 = 7 = 7
example : (4 + 1)^2 - 4^2 = 2 * 4 + 1 := by native_decide  -- 25 - 16 = 9 = 9
```

**수학적 배경**: (n+1)² - n² = n² + 2n + 1 - n² = 2n + 1

</details>

---

## 4-5.4 교재 예제: 경우에 의한 증명 (예제 3)

### 4-5.4.1 문제

> **예제 3** (Rosen 1.8절):  
> n이 정수이면 n² ≥ n임을 증명하라.

### 4-5.4.2 왜 전수 증명이 안 되는가?

정수는 **무한히 많다**! 

..., -3, -2, -1, 0, 1, 2, 3, ...

모든 정수를 일일이 검사할 수 없으므로, **경우에 의한 증명**을 사용해야 한다.

### 4-5.4.3 경우 분류

모든 정수를 세 가지 경우로 분류한다:

| 경우 | 조건 | 예시 |
|------|------|-----|
| (i) | n = 0 | 0 |
| (ii) | n ≥ 1 (양의 정수) | 1, 2, 3, ... |
| (iii) | n ≤ -1 (음의 정수) | -1, -2, -3, ... |

**이 세 경우가 모든 정수를 망라하는가?**

어떤 정수 n이든:
- n = 0이거나
- n > 0 (즉, n ≥ 1)이거나
- n < 0 (즉, n ≤ -1)이다

예외 없이 **모든 정수**가 이 세 경우 중 하나에 속한다! ✓

### 4-5.4.4 상세 풀이

**경우 (i)**: n = 0일 때

$$n^2 = 0^2 = 0$$
$$n = 0$$
$$0 \geq 0 \quad \checkmark$$

**경우 (ii)**: n ≥ 1일 때

n ≥ 1이면:
$$n^2 = n \cdot n \geq n \cdot 1 = n$$

왜냐하면 n ≥ 1이므로 n · n ≥ n · 1이다.

따라서 n² ≥ n ✓

**경우 (iii)**: n ≤ -1일 때

n ≤ -1 < 0이므로 n은 **음수**이다.

그런데 **제곱은 항상 음이 아닌 수**이다: n² ≥ 0

음수 n에 대해 n < 0이므로:
$$n^2 \geq 0 > n$$

따라서 n² ≥ n ✓

### 4-5.4.5 결론

세 경우 **모두**에서 n² ≥ n이 성립한다.

세 경우가 모든 정수를 망라하므로, **모든 정수 n에 대해** n² ≥ n이 성립한다!

---

## 4-5.5 Lean4에서 경우에 의한 증명

### 4-5.5.1 `cases` 전술 기초

`cases` 전술은 **귀납적 타입**이나 **논리합**을 **경우별로 분해**한다.

**기본 문법**:
```lean
cases h with
| case1 => -- 첫 번째 경우의 증명
| case2 => -- 두 번째 경우의 증명
```

### 4-5.5.2 논리합(Or)에 대한 cases

```lean
-- h : P ∨ Q가 주어졌을 때, 두 경우로 분해
example (P Q R : Prop) (h : P ∨ Q) (hp : P → R) (hq : Q → R) : R := by
  cases h with
  | inl p =>          -- 첫 번째 경우: P가 참 (p : P를 얻음)
    exact hp p        -- P → R에 P를 적용하여 R
  | inr q =>          -- 두 번째 경우: Q가 참 (q : Q를 얻음)
    exact hq q        -- Q → R에 Q를 적용하여 R
```

**명칭 설명**:
- `inl`: "injection left" - 논리합의 **왼쪽** 구성요소
- `inr`: "injection right" - 논리합의 **오른쪽** 구성요소

### 4-5.5.3 cases 전술 상세 분석

```lean
-- 단계별로 상태 확인
example (P Q R : Prop) (h : P ∨ Q) (hp : P → R) (hq : Q → R) : R := by
  cases h with
  | inl p =>
    -- 현재 컨텍스트:
    -- P Q R : Prop
    -- p : P          ← 새로 얻은 가정!
    -- hp : P → R
    -- hq : Q → R
    -- ⊢ R            ← 증명할 목표
    exact hp p
  | inr q =>
    -- 현재 컨텍스트:
    -- P Q R : Prop
    -- q : Q          ← 새로 얻은 가정!
    -- hp : P → R
    -- hq : Q → R
    -- ⊢ R            ← 증명할 목표
    exact hq q
```

### 4-5.5.4 `rcases` 전술: 더 유연한 패턴 매칭

`rcases`(recursive cases)는 **중첩된 구조**를 **한 번에** 분해할 수 있다.

```lean
-- rcases 기본 문법
-- rcases h with pattern1 | pattern2 | ...

-- 논리합 분해
example (P Q R : Prop) (h : P ∨ Q) (hp : P → R) (hq : Q → R) : R := by
  rcases h with p | q    -- h를 p : P 또는 q : Q로 분해
  · exact hp p           -- P인 경우 (· 는 중점)
  · exact hq q           -- Q인 경우
```

### 4-5.5.5 논리곱(And)에 대한 rcases

```lean
-- h : P ∧ Q를 분해
example (P Q : Prop) (h : P ∧ Q) : P := by
  rcases h with ⟨hp, hq⟩   -- h를 hp : P와 hq : Q로 분해
  -- hp : P
  -- hq : Q
  exact hp

-- ⟨ ⟩ 는 angle brackets, 키보드로 \< \> 또는 \langle \rangle
```

### 4-5.5.6 중첩 구조 분해

```lean
-- (P ∧ Q) ∨ R 형태의 복잡한 구조
example (P Q R : Prop) (h : (P ∧ Q) ∨ R) : P ∨ R := by
  rcases h with ⟨hp, hq⟩ | hr
  -- 경우 1: P ∧ Q인 경우 → hp : P, hq : Q
  · left          -- P ∨ R의 왼쪽(P) 선택
    exact hp
  -- 경우 2: R인 경우 → hr : R
  · right         -- P ∨ R의 오른쪽(R) 선택
    exact hr
```

### 4-5.5.7 `·` (중점) 문법 설명

Lean4에서 `·`(middle dot, 키보드로 `\.` 또는 중점 문자)는 **구조화된 증명 블록**을 시작한다.

```lean
-- · 사용 예
example (P Q : Prop) (h : P ∨ Q) : Q ∨ P := by
  rcases h with hp | hq
  · -- 첫 번째 경우 블록 시작
    right       -- 목표: P (Q ∨ P의 오른쪽)
    exact hp
  · -- 두 번째 경우 블록 시작
    left        -- 목표: Q (Q ∨ P의 왼쪽)
    exact hq
```

### 4-5.5.8 `left`와 `right` 전술

논리합 P ∨ Q를 **증명**할 때 사용:

| 전술 | 의미 | 새 목표 |
|-----|------|--------|
| `left` | 왼쪽 선택 | P |
| `right` | 오른쪽 선택 | Q |

```lean
-- P가 참이면 P ∨ Q도 참
example (P Q : Prop) (hp : P) : P ∨ Q := by
  left       -- "나는 왼쪽(P)을 증명하겠다"
  exact hp   -- P 증명

-- Q가 참이면 P ∨ Q도 참
example (P Q : Prop) (hq : Q) : P ∨ Q := by
  right      -- "나는 오른쪽(Q)을 증명하겠다"
  exact hq   -- Q 증명
```

### 4-5.5.9 Or.inl과 Or.inr 직접 사용

`left`와 `right` 대신 `Or.inl`과 `Or.inr`을 직접 사용할 수도 있다:

```lean
-- Or.inl : P → P ∨ Q (왼쪽 주입)
-- Or.inr : Q → P ∨ Q (오른쪽 주입)

example (P Q : Prop) (hp : P) : P ∨ Q := Or.inl hp
example (P Q : Prop) (hq : Q) : P ∨ Q := Or.inr hq
```

---

### 4-5.5.10 연습문제 2: 경우에 의한 증명 기초

#### 연습 2-1: 논리합 분해와 재구성
```lean
-- P ∨ Q가 주어졌을 때 Q ∨ P를 증명하라 (논리합의 교환법칙)
example (P Q : Prop) (h : P ∨ Q) : Q ∨ P := by
  cases h with
  | inl hp => sorry   -- P인 경우
  | inr hq => sorry   -- Q인 경우
```

<details>
<summary>💡 답 보기</summary>

```lean
example (P Q : Prop) (h : P ∨ Q) : Q ∨ P := by
  cases h with
  | inl hp =>         -- hp : P
    right             -- 목표: Q ∨ P의 오른쪽(P) 선택
    exact hp
  | inr hq =>         -- hq : Q
    left              -- 목표: Q ∨ P의 왼쪽(Q) 선택
    exact hq
```

**설명**:
- `inl hp`: `h : P ∨ Q`에서 왼쪽(P)인 경우, `hp : P`를 얻음
- `inr hq`: 오른쪽(Q)인 경우, `hq : Q`를 얻음
- `right`: `Q ∨ P`의 오른쪽(P)을 선택하여 증명
- `left`: `Q ∨ P`의 왼쪽(Q)을 선택하여 증명

</details>

#### 연습 2-2: rcases 사용
```lean
-- 같은 문제를 rcases로 풀어라
example (P Q : Prop) (h : P ∨ Q) : Q ∨ P := by
  rcases h with hp | hq
  · sorry   -- P인 경우
  · sorry   -- Q인 경우
```

<details>
<summary>💡 답 보기</summary>

```lean
example (P Q : Prop) (h : P ∨ Q) : Q ∨ P := by
  rcases h with hp | hq
  · right; exact hp    -- P인 경우: Q ∨ P의 오른쪽
  · left; exact hq     -- Q인 경우: Q ∨ P의 왼쪽
```

**설명**: `rcases h with hp | hq`는 `h : P ∨ Q`를 `hp : P` 또는 `hq : Q`로 분해한다. 세미콜론(`;`)은 전술을 연속해서 적용한다.

</details>

#### 연습 2-3: 세 가지 경우
```lean
-- P ∨ Q ∨ R이 주어졌을 때, 각각이 S를 함의하면 S가 참
example (P Q R S : Prop) (h : P ∨ Q ∨ R) 
    (hp : P → S) (hq : Q → S) (hr : R → S) : S := by
  rcases h with p | q | r
  · sorry   -- P인 경우
  · sorry   -- Q인 경우
  · sorry   -- R인 경우
```

<details>
<summary>💡 답 보기</summary>

```lean
example (P Q R S : Prop) (h : P ∨ Q ∨ R) 
    (hp : P → S) (hq : Q → S) (hr : R → S) : S := by
  rcases h with p | q | r
  · exact hp p    -- P인 경우: P → S에 P 적용
  · exact hq q    -- Q인 경우: Q → S에 Q 적용
  · exact hr r    -- R인 경우: R → S에 R 적용
```

**설명**: `P ∨ Q ∨ R`은 `P ∨ (Q ∨ R)`로 해석되며, `rcases`는 이를 세 가지 경우로 분해한다.

</details>

#### 연습 2-4: 논리곱에서 추출
```lean
-- P ∧ Q ∧ R이 주어졌을 때 Q를 추출하라
example (P Q R : Prop) (h : P ∧ Q ∧ R) : Q := by
  rcases h with ⟨hp, hq, hr⟩
  sorry
```

<details>
<summary>💡 답 보기</summary>

```lean
example (P Q R : Prop) (h : P ∧ Q ∧ R) : Q := by
  rcases h with ⟨hp, hq, hr⟩
  -- hp : P, hq : Q, hr : R
  exact hq
```

**설명**: `P ∧ Q ∧ R`은 `P ∧ (Q ∧ R)`로 해석된다. `⟨hp, hq, hr⟩` 패턴은 중첩된 논리곱을 한 번에 분해한다.

</details>

#### 연습 2-5: 혼합 구조 분해
```lean
-- (P ∧ Q) ∨ (P ∧ R)이면 P임을 증명하라
example (P Q R : Prop) (h : (P ∧ Q) ∨ (P ∧ R)) : P := by
  rcases h with ⟨hp, hq⟩ | ⟨hp, hr⟩
  · sorry   -- P ∧ Q인 경우
  · sorry   -- P ∧ R인 경우
```

<details>
<summary>💡 답 보기</summary>

```lean
example (P Q R : Prop) (h : (P ∧ Q) ∨ (P ∧ R)) : P := by
  rcases h with ⟨hp, hq⟩ | ⟨hp, hr⟩
  · exact hp    -- P ∧ Q에서 hp : P 추출
  · exact hp    -- P ∧ R에서 hp : P 추출
```

**설명**: 두 경우 모두에서 `hp : P`를 얻으므로 바로 사용할 수 있다.

</details>

#### 연습 2-6: 분배법칙 형태
```lean
-- P ∧ (Q ∨ R)이면 (P ∧ Q) ∨ (P ∧ R)임을 증명하라
-- 이것은 논리곱의 논리합에 대한 분배법칙!
example (P Q R : Prop) (h : P ∧ (Q ∨ R)) : (P ∧ Q) ∨ (P ∧ R) := by
  rcases h with ⟨hp, hqr⟩
  rcases hqr with hq | hr
  · sorry   -- Q인 경우
  · sorry   -- R인 경우
```

<details>
<summary>💡 답 보기</summary>

```lean
example (P Q R : Prop) (h : P ∧ (Q ∨ R)) : (P ∧ Q) ∨ (P ∧ R) := by
  rcases h with ⟨hp, hqr⟩
  -- hp : P, hqr : Q ∨ R
  rcases hqr with hq | hr
  · -- Q인 경우: P ∧ Q를 구성
    left
    exact ⟨hp, hq⟩
  · -- R인 경우: P ∧ R을 구성
    right
    exact ⟨hp, hr⟩
```

**설명**: `⟨hp, hq⟩`는 `P ∧ Q`를 구성하는 익명 생성자이다.

</details>

---

### 4-5.5.11 연습문제 3: 수 타입에서의 경우 분해

#### 연습 3-1: 자연수의 경우
```lean
-- Nat.eq_zero_or_pos : ∀ n : Nat, n = 0 ∨ n > 0
-- 이를 이용하여 다음을 증명하라

example (n : Nat) : n = 0 ∨ n ≥ 1 := by
  rcases Nat.eq_zero_or_pos n with h | h
  · sorry   -- n = 0인 경우
  · sorry   -- n > 0인 경우
```

<details>
<summary>💡 답 보기</summary>

```lean
example (n : Nat) : n = 0 ∨ n ≥ 1 := by
  rcases Nat.eq_zero_or_pos n with h | h
  · -- h : n = 0
    left
    exact h
  · -- h : n > 0, 즉 n ≥ 1
    right
    exact h   -- Nat에서 n > 0 ↔ n ≥ 1
```

</details>

#### 연습 3-2: 짝수 또는 홀수
```lean
-- 모든 자연수는 짝수이거나 홀수이다
-- Nat.even_or_odd : ∀ n : Nat, Even n ∨ Odd n

-- n이 짝수이거나 n + 1이 짝수이다
example (n : Nat) : Even n ∨ Even (n + 1) := by
  rcases Nat.even_or_odd n with he | ho
  · sorry   -- n이 짝수인 경우
  · sorry   -- n이 홀수인 경우
```

<details>
<summary>💡 답 보기</summary>

```lean
example (n : Nat) : Even n ∨ Even (n + 1) := by
  rcases Nat.even_or_odd n with he | ho
  · -- n이 짝수인 경우
    left
    exact he
  · -- n이 홀수인 경우: n + 1은 짝수
    right
    exact Nat.Odd.add_one ho
```

**설명**: 홀수에 1을 더하면 짝수가 된다!

</details>

---

## 4-5.6 교재 예제: 절댓값 증명 (예제 4)

### 4-5.6.1 문제

> **예제 4** (Rosen 1.8절):  
> |xy| = |x||y|임을 경우에 의한 증명 방법으로 증명하라.

### 4-5.6.2 절댓값의 정의

실수 a의 **절댓값**(absolute value) |a|:

$$|a| = \begin{cases} a & \text{if } a \geq 0 \\ -a & \text{if } a < 0 \end{cases}$$

### 4-5.6.3 경우 분류

x와 y의 **부호**에 따라 **네 가지 경우**가 있다:

| 경우 | x의 부호 | y의 부호 | xy의 부호 |
|------|---------|---------|----------|
| (i) | x ≥ 0 | y ≥ 0 | xy ≥ 0 |
| (ii) | x ≥ 0 | y < 0 | xy ≤ 0 |
| (iii) | x < 0 | y ≥ 0 | xy ≤ 0 |
| (iv) | x < 0 | y < 0 | xy > 0 |

### 4-5.6.4 상세 풀이

**경우 (i)**: x ≥ 0, y ≥ 0

- |x| = x (정의에 의해, x ≥ 0이므로)
- |y| = y (정의에 의해, y ≥ 0이므로)
- xy ≥ 0 (두 음이 아닌 수의 곱)
- |xy| = xy (정의에 의해, xy ≥ 0이므로)

따라서: |xy| = xy = x · y = |x| · |y| ✓

**경우 (ii)**: x ≥ 0, y < 0

- |x| = x
- |y| = -y (정의에 의해, y < 0이므로)
- xy ≤ 0 (양수 × 음수 = 음수 또는 0)
- |xy| = -xy (정의에 의해, xy ≤ 0이므로)

따라서: |xy| = -xy = x · (-y) = |x| · |y| ✓

**경우 (iii)**: x < 0, y ≥ 0

- |x| = -x
- |y| = y
- xy ≤ 0
- |xy| = -xy

따라서: |xy| = -xy = (-x) · y = |x| · |y| ✓

**경우 (iv)**: x < 0, y < 0

- |x| = -x
- |y| = -y
- xy > 0 (음수 × 음수 = 양수)
- |xy| = xy

따라서: |xy| = xy = (-x) · (-y) = |x| · |y| ✓

**결론**: 네 가지 경우 모두에서 |xy| = |x||y|가 성립한다. ∎

---

## 4-5.7 일반성을 잃지 않고 (WLOG)

### 4-5.7.1 WLOG란?

**"일반성을 잃지 않고"**(Without Loss Of Generality, **WLOG**)는 **대칭성**을 이용하여 **경우의 수를 줄이는** 기법이다.

### 4-5.7.2 예제 4에서의 WLOG

예제 4에서 경우 (ii)와 (iii)을 비교해 보자:

| | 경우 (ii) | 경우 (iii) |
|--|---------|----------|
| 조건 | x ≥ 0, y < 0 | x < 0, y ≥ 0 |
| |x| | x | -x |
| |y| | -y | y |

경우 (iii)은 경우 (ii)에서 **x와 y를 바꾼 것**과 같다!

|xy| = |x||y|에서 x와 y의 역할은 **대칭적**이므로:
- |xy| = |yx| (곱셈의 교환법칙)
- |x||y| = |y||x| (곱셈의 교환법칙)

따라서:
> "**일반성을 잃지 않고** x ≥ 0, y < 0인 경우(ii)만 증명하면, 경우(iii)은 x와 y를 바꾸어 같은 논증으로 증명된다."

### 4-5.7.3 WLOG 사용 조건

WLOG를 사용할 수 있는 조건:

1. 증명하려는 명제가 변수들에 대해 **대칭적**이어야 함
2. 경우들이 변수 **교환으로 서로 변환 가능**해야 함
3. 한 경우의 증명이 다른 경우에 **그대로 적용 가능**해야 함

### 4-5.7.4 WLOG의 올바른 사용 예

**예시 1**: "x + y = y + x를 증명하라"
> WLOG 필요 없음 - 바로 덧셈의 교환법칙!

**예시 2**: "양의 실수 x, y에 대해 x + y ≥ 2√(xy)임을 증명하라"
> x와 y의 역할이 대칭적이므로, WLOG x ≤ y라 가정할 수 있다.

**예시 3**: "max(x, y) + min(x, y) = x + y를 증명하라"
> WLOG x ≤ y라 가정하면 max(x,y) = y, min(x,y) = x이므로
> y + x = x + y ✓

### 4-5.7.5 WLOG의 잘못된 사용

**잘못된 예**: "x < y를 증명하라"에서 "WLOG x ≤ 0이라 가정"
→ x의 부호와 x < y는 **관련이 없음**!

**잘못된 예**: "x² + y² ≥ 2xy를 증명하라"에서 "WLOG x = y"
→ 일반적인 경우를 특수한 경우로 축소하면 **일반성을 잃음**!

### 4-5.7.6 Lean4에서 대칭성 활용

```lean
-- 덧셈의 교환법칙
example (a b : Nat) (h : a + b = 10) : b + a = 10 := by
  rw [Nat.add_comm]   -- b + a를 a + b로 재작성
  exact h

-- 곱셈의 교환법칙
example (x y : Int) (h : x * y = 0) : y * x = 0 := by
  rw [Int.mul_comm]
  exact h

-- max의 교환법칙
example (a b : Nat) : max a b = max b a := by
  exact Nat.max_comm a b
```

---

### 4-5.7.7 연습문제 4: 대칭성과 WLOG

#### 연습 4-1: 덧셈 대칭성
```lean
-- a + b + c = c + b + a 증명
example (a b c : Nat) : a + b + c = c + b + a := by
  sorry
```

<details>
<summary>💡 답 보기</summary>

```lean
example (a b c : Nat) : a + b + c = c + b + a := by
  ring
  -- 또는: omega
```

**설명**: `ring` 전술은 덧셈과 곱셈의 대수적 성질(교환법칙, 결합법칙, 분배법칙)을 자동으로 적용한다.

</details>

#### 연습 4-2: 곱셈 대칭성
```lean
-- x * y * z = z * y * x 증명
example (x y z : Int) : x * y * z = z * y * x := by
  sorry
```

<details>
<summary>💡 답 보기</summary>

```lean
example (x y z : Int) : x * y * z = z * y * x := by
  ring
```

</details>

#### 연습 4-3: max와 min의 대칭성
```lean
-- max(a, b) = max(b, a)
example (a b : Nat) : max a b = max b a := by
  sorry
```

<details>
<summary>💡 답 보기</summary>

```lean
example (a b : Nat) : max a b = max b a := by
  exact Nat.max_comm a b
  -- 또는: simp [max_comm]
```

</details>

---

## 4-5.8 존재 증명의 기초

### 4-5.8.1 존재 명제란?

**존재 명제**(existential statement)는 "어떤 조건을 만족시키는 것이 **존재한다**"는 주장이다.

형식적으로: ∃x P(x)

읽는 방법: "P(x)를 만족하는 x가 존재한다" 또는 "어떤 x에 대해 P(x)이다"

### 4-5.8.2 존재 증명이란?

**존재 증명**(existence proof)은 ∃x P(x)가 참임을 보이는 것이다.

가장 직접적인 방법: P(a)가 **참인** 어떤 특정 값 a를 찾아내는 것!

이런 a를 **증인**(witness)이라 한다.

### 4-5.8.3 생산적 증명 vs 비생산적 증명

| 유형 | 영문 | 설명 | 증인 제시 |
|-----|-----|------|---------|
| **생산적** | Constructive | 실제로 증인을 **구체적으로** 찾아냄 | ✓ 있음 |
| **비생산적** | Nonconstructive | 존재는 보이지만 **구체적 예시 없음** | ✗ 없음 |

### 4-5.8.4 생산적 증명 예시

**문제**: "x² = 9를 만족하는 자연수 x가 존재한다"를 증명하라.

**생산적 증명**:
> x = 3을 선택한다.
> 
> 검증: 3² = 9 ✓
> 
> 따라서 조건을 만족하는 x가 존재한다. ∎

**증인**: x = 3

---

## 4-5.9 교재 예제: 라마누잔 수 (예제 10)

### 4-5.9.1 문제

> **예제 10** (Rosen 1.8절):  
> 두 가지 다른 형태로 양의 정수 3제곱들의 합으로 나타낼 수 있는 양의 정수가 존재함을 증명하라.

### 4-5.9.2 생산적 증명

$$1729 = 10^3 + 9^3 = 12^3 + 1^3$$

**검증**:
- 10³ + 9³ = 1000 + 729 = 1729 ✓
- 12³ + 1³ = 1728 + 1 = 1729 ✓
- {10, 9} ≠ {12, 1}이므로 두 표현은 다름 ✓

**증인**: n = 1729, (a, b) = (10, 9), (c, d) = (12, 1)

### 4-5.9.3 라마누잔 수의 역사

이 예제에는 유명한 일화가 있다!

영국의 수학자 **G. H. 하디**(Godfrey Harold Hardy)가 병원에 입원 중인 인도의 천재 수학자 **스리니바사 라마누잔**(Srinivasa Ramanujan, 1887-1920)을 방문했다. 

하디가 타고 온 택시 번호가 1729였는데, 하디가 "별 의미 없는 숫자군요"라고 하자, 라마누잔은 즉시 대답했다:

> "아닙니다! 그것은 **두 가지의 다른 방법으로 두 세제곱수의 합으로 나타낼 수 있는 가장 작은 수**입니다."

1729는 이후 **라마누잔 수**(Ramanujan number) 또는 **택시캡 수**(taxicab number)라 불린다.

### 4-5.9.4 Lean4로 라마누잔 수 증명

```lean
-- 계산 확인
#eval 10^3 + 9^3     -- 1729
#eval 12^3 + 1^3     -- 1729
#eval 10^3           -- 1000
#eval 9^3            -- 729
#eval 12^3           -- 1728

-- 두 표현이 같은 값을 가짐
example : 10^3 + 9^3 = 1729 := by native_decide
example : 12^3 + 1^3 = 1729 := by native_decide

-- 존재 증명
example : ∃ n : Nat, ∃ a b c d : Nat, 
    (a, b) ≠ (c, d) ∧ n = a^3 + b^3 ∧ n = c^3 + d^3 := by
  use 1729, 10, 9, 12, 1
  native_decide
```

---

## 4-5.10 교재 예제: 무리수의 무리수 제곱 (예제 11)

### 4-5.10.1 문제

> **예제 11** (Rosen 1.8절):  
> $x^y$가 유리수가 되는 무리수 x와 y가 존재함을 증명하라.

### 4-5.10.2 비생산적 증명

$\sqrt{2}^{\sqrt{2}}$를 생각해 보자.

**경우 1**: $\sqrt{2}^{\sqrt{2}}$가 **유리수**인 경우

- x = √2 (무리수)
- y = √2 (무리수)
- x^y = √2^√2 (가정에 의해 유리수)

조건을 만족한다! ✓

**경우 2**: √2^√2가 **무리수**인 경우

- x = √2^√2 (가정에 의해 무리수)
- y = √2 (무리수)
- x^y = (√2^√2)^√2

지수 법칙 (a^m)^n = a^(mn)에 의해:
$$x^y = \sqrt{2}^{\sqrt{2} \cdot \sqrt{2}} = \sqrt{2}^2 = 2$$

2는 유리수이므로 조건을 만족한다! ✓

**결론**: 두 경우 중 **하나가 반드시** 성립하므로, 조건을 만족하는 (x, y)가 **존재**한다!

### 4-5.10.3 비생산적 증명의 특징

**핵심 관찰**:
1. 조건을 만족하는 (x, y)가 **존재함**은 확실히 증명됨
2. 그러나 **어느 경우인지 모름**!
   - √2^√2가 유리수인지 무리수인지 이 증명에서는 결정 안 함
3. **구체적인 증인을 제시하지 않음**

**참고**: 실제로 √2^√2는 **무리수**임이 알려져 있다 (Gelfond-Schneider 정리, 1934년). 따라서 경우 2가 실제로 성립한다.

---

## 4-5.11 Lean4에서 존재 증명

### 4-5.11.1 `use` 전술: 증인 제공

`use` 전술은 존재 명제 ∃x, P(x)를 증명할 때 **구체적인 증인**을 제공한다.

```lean
-- 기본 문법
-- use a       -- a를 증인으로 제시
-- 이후 P(a)를 증명해야 함
```

### 4-5.11.2 `use` 상세 분석

```lean
-- 예제: x + 5 = 8을 만족하는 자연수 x가 존재한다
example : ∃ x : Nat, x + 5 = 8 := by
  use 3          -- 증인으로 3을 제시
  -- 이제 목표는 3 + 5 = 8
  native_decide

-- 더 복잡한 예: 조건이 여러 개
example : ∃ x : Nat, x > 5 ∧ x < 10 ∧ x % 2 = 0 := by
  use 6           -- 6은 5보다 크고 10보다 작은 짝수
  constructor
  · native_decide   -- 6 > 5
  · constructor
    · native_decide -- 6 < 10
    · native_decide -- 6 % 2 = 0
```

### 4-5.11.3 여러 존재 한정기호

```lean
-- 두 개의 존재 한정기호
-- ∃ x y, P(x, y)를 증명하려면 use를 두 번 사용
example : ∃ x y : Nat, x + y = 10 ∧ x * y = 21 := by
  use 3, 7        -- x = 3, y = 7
  constructor
  · native_decide -- 3 + 7 = 10
  · native_decide -- 3 * 7 = 21

-- 또는 따로따로
example : ∃ x y : Nat, x + y = 10 ∧ x * y = 21 := by
  use 3
  use 7
  native_decide
```

### 4-5.11.4 `obtain` 전술: 존재 명제 분해

존재 명제가 **가설로 주어졌을 때**, `obtain`을 사용하여 **증인과 성질을 추출**한다.

```lean
-- 기본 문법
-- obtain ⟨a, ha⟩ := h
-- h : ∃ x, P(x)로부터
-- a : 타입, ha : P(a)를 얻음
```

### 4-5.11.5 `obtain` 상세 분석

```lean
-- 예제: 존재에서 존재로
example (h : ∃ x : Nat, x * x = 16) : ∃ y : Nat, y + 12 = 16 := by
  obtain ⟨x, hx⟩ := h
  -- x : Nat
  -- hx : x * x = 16
  use 4
  native_decide

-- 예제: 추출한 증인 활용
example (h : ∃ x : Nat, x > 10) : ∃ y : Nat, y > 5 := by
  obtain ⟨x, hx⟩ := h
  -- x : Nat, hx : x > 10
  use x           -- 같은 x를 증인으로 사용
  omega           -- x > 10이면 x > 5
```

---

### 4-5.11.6 연습문제 5: 존재 증명 기초

#### 연습 5-1: 간단한 존재 증명
```lean
-- x + 5 = 12를 만족하는 자연수 x가 존재
example : ∃ x : Nat, x + 5 = 12 := by
  sorry
```

<details>
<summary>💡 답 보기</summary>

```lean
example : ∃ x : Nat, x + 5 = 12 := by
  use 7
  native_decide  -- 7 + 5 = 12
```

</details>

#### 연습 5-2: 제곱 방정식
```lean
-- x² = 16을 만족하는 자연수 x가 존재
example : ∃ x : Nat, x^2 = 16 := by
  sorry
```

<details>
<summary>💡 답 보기</summary>

```lean
example : ∃ x : Nat, x^2 = 16 := by
  use 4
  native_decide
```

</details>

#### 연습 5-3: 복합 조건
```lean
-- 10보다 크고 20보다 작은 짝수가 존재
example : ∃ n : Nat, n > 10 ∧ n < 20 ∧ n % 2 = 0 := by
  sorry
```

<details>
<summary>💡 답 보기</summary>

```lean
example : ∃ n : Nat, n > 10 ∧ n < 20 ∧ n % 2 = 0 := by
  use 12
  native_decide
```

</details>

#### 연습 5-4: 두 변수의 존재
```lean
-- x + y = 10이고 x * y = 21인 자연수 x, y가 존재
example : ∃ x y : Nat, x + y = 10 ∧ x * y = 21 := by
  sorry
```

<details>
<summary>💡 답 보기</summary>

```lean
example : ∃ x y : Nat, x + y = 10 ∧ x * y = 21 := by
  use 3, 7
  native_decide
```

</details>

#### 연습 5-5: 소수 존재
```lean
-- 20보다 크고 25보다 작은 소수가 존재
example : ∃ p : Nat, p > 20 ∧ p < 25 ∧ Nat.Prime p := by
  sorry
```

<details>
<summary>💡 답 보기</summary>

```lean
example : ∃ p : Nat, p > 20 ∧ p < 25 ∧ Nat.Prime p := by
  use 23
  native_decide
```

</details>

#### 연습 5-6: 피타고라스 삼중수
```lean
-- a² + b² = c²를 만족하는 양의 정수 a, b, c가 존재
example : ∃ a b c : Nat, a > 0 ∧ b > 0 ∧ c > 0 ∧ a^2 + b^2 = c^2 := by
  sorry
```

<details>
<summary>💡 답 보기</summary>

```lean
example : ∃ a b c : Nat, a > 0 ∧ b > 0 ∧ c > 0 ∧ a^2 + b^2 = c^2 := by
  use 3, 4, 5
  native_decide
```

**검증**: 3² + 4² = 9 + 16 = 25 = 5² ✓

</details>

#### 연습 5-7: obtain 사용
```lean
-- h : ∃ x, x + 3 = 10이 주어졌을 때, ∃ y, y > 5 증명
example (h : ∃ x : Nat, x + 3 = 10) : ∃ y : Nat, y > 5 := by
  obtain ⟨x, hx⟩ := h
  sorry
```

<details>
<summary>💡 답 보기</summary>

```lean
example (h : ∃ x : Nat, x + 3 = 10) : ∃ y : Nat, y > 5 := by
  obtain ⟨x, hx⟩ := h
  use x
  omega  -- x + 3 = 10이면 x = 7 > 5
```

</details>

---

**(Part B에서 계속: 유일성 증명, 전향/후향 추론, 반례, 종합 연습문제)**
