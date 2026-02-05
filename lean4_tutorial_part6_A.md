# Lean4 Tutorial Part 6-A: **알고리즘**(Algorithms)과 Lean4 — 기초편

> **기반 교재**: Kenneth H. Rosen, *Discrete Mathematics and Its Applications* 8판 3.1절  
> **참고 교재**: *Mathematics in Lean* Chapter 2, 5, 6  
> **선수 지식**: Part 5까지의 내용 (정리, 보조정리, rw, apply, exact, cases 등)

---

## 6A.0 이 파트에서 배우는 것

이 파트에서는 다음을 학습한다:

1. **알고리즘**(algorithm)이란 무엇인가 — Lean4에서 알고리즘은 **함수**(function)로 표현된다
2. Lean4에서 **함수를 정의하는 법** — `def`, 패턴 매칭(pattern matching), **재귀**(recursion)
3. **자연수**(Nat)와 **리스트**(List)의 기본 구조 — 알고리즘의 입력과 출력
4. **선형 탐색**(linear search) 알고리즘을 Lean4로 구현하고 검증하는 법
5. **정리**(theorem)와 **보조정리**(lemma)의 관계 복습 — 알고리즘의 **정확성**(correctness) 증명

**핵심 관점**: Rosen 교재의 **의사 코드**(pseudocode)는 "사람이 읽는 알고리즘"이다. Lean4의 **함수 정의**는 "컴퓨터가 읽고 + 수학적으로 검증 가능한 알고리즘"이다. 이 둘은 같은 것을 다른 방식으로 표현한 것이다.

---

## 6A.1 **알고리즘**(Algorithm)이란?

### 교재 정의 (Rosen 3.1절)

Rosen 교재에서 **알고리즘**의 정의는 다음과 같다:

> **알고리즘**은 계산을 하거나, 문제를 풀기 위한 **정확한 명령의 유한한 서열**이다.

이 정의에는 핵심 단어가 세 가지 있다:

| 핵심 단어 | 의미 | Lean4에서의 대응 |
|-----------|------|----------------|
| **정확한**(precise) | 각 단계가 명확하게 정의되어야 한다 | 함수 정의의 각 줄이 정확한 연산이다 |
| **명령의**(instructions) | 수행해야 할 동작을 나타낸다 | Lean4의 각 표현식(expression)이 명령이다 |
| **유한한**(finite) | 단계가 끝나야 한다 — 무한히 계속되면 안 된다 | Lean4는 함수가 **반드시 종료**함을 보장한다 |

### 알고리즘의 속성 7가지

Rosen 교재에서는 알고리즘이 갖춰야 할 속성을 다음과 같이 나열한다:

1. **입력**(input) — 특정한 집합으로부터 입력값을 받는다
2. **출력**(output) — 각 입력에 대해 출력값을 생성한다
3. **명확성**(definiteness) — 각 단계가 명확하게 정의되어야 한다
4. **정확성**(correctness) — 어떤 입력에 대해서도 항상 정답을 구해야 한다
5. **유한성**(finiteness) — 어떤 입력에 대해서도 유한한 횟수의 단계를 거쳐 답을 내야 한다
6. **효율성**(effectiveness) — 각 단계를 정확하고 유한한 시간에 수행할 수 있어야 한다
7. **일반성**(generality) — 특정 입력뿐 아니라 조건을 만족하는 모든 입력에 적용되어야 한다

이 속성들을 Lean4의 관점에서 다시 보면:

| 속성 | Lean4에서의 의미 |
|------|----------------|
| 입력 | 함수의 **매개변수**(parameter)와 그 **타입**(type) |
| 출력 | 함수의 **반환 타입**(return type) |
| 명확성 | Lean4는 **모호한 정의**를 허용하지 않는다 — 타입 검사(type checking)가 이를 보장 |
| 정확성 | **정리**(theorem)를 통해 수학적으로 증명할 수 있다 |
| 유한성 | Lean4의 **종료 검사기**(termination checker)가 보장한다 |
| 효율성 | `#eval`로 실제 실행하여 확인할 수 있다 |
| 일반성 | **타입 다형성**(polymorphism) — `α`처럼 어떤 타입에도 적용 가능 |

---

## 6A.2 Lean4에서 **함수**(Function) 정의하기 — `def`

### 기본 형태

Lean4에서 함수를 정의하는 가장 기본적인 형태이다:

```lean
def 함수이름 (매개변수 : 타입) : 반환타입 :=
  본문
```

가장 간단한 예시부터 시작한다:

```lean
-- 두 자연수를 더하는 함수
def myAdd (a : Nat) (b : Nat) : Nat :=
  a + b

#eval myAdd 3 5  -- 결과: 8
```

이 코드를 한 줄씩 분석해 보자:

| 코드 조각 | 의미 |
|-----------|------|
| `def` | "이제 새로운 정의를 하겠다"는 선언 |
| `myAdd` | 이 함수의 이름 |
| `(a : Nat)` | 첫 번째 입력 — 이름은 `a`, 타입은 자연수(`Nat`) |
| `(b : Nat)` | 두 번째 입력 — 이름은 `b`, 타입은 자연수(`Nat`) |
| `: Nat` | 출력의 타입 — 자연수(`Nat`) |
| `:=` | "다음이 정의의 본문이다"라는 기호 |
| `a + b` | 실제 계산 — 두 입력을 더한다 |

### `#eval`로 실행하기

Lean4에서는 `#eval` 명령으로 함수를 즉시 실행할 수 있다:

```lean
#eval myAdd 3 5      -- 8
#eval myAdd 100 200  -- 300
#eval myAdd 0 0      -- 0
```

이것은 Rosen 교재에서 알고리즘을 **추적**(trace)하는 것과 같다. 교재에서는 입력 8, 4, 11, 3, 10에 대해 알고리즘을 단계별로 따라가는데, Lean4에서는 `#eval`이 이 작업을 자동으로 수행한다.

### 예시: 더 많은 함수들

```lean
-- 두 수 중 더 큰 것을 반환
def myMax (a : Nat) (b : Nat) : Nat :=
  if a ≥ b then a else b

#eval myMax 7 3   -- 7
#eval myMax 2 9   -- 9
#eval myMax 5 5   -- 5

-- 세 수 중 가장 큰 것을 반환
def max3 (a b c : Nat) : Nat :=
  myMax (myMax a b) c

#eval max3 3 7 5  -- 7
#eval max3 1 1 1  -- 1
```

여기서 `max3`는 `myMax`를 **두 번** 호출하여 결과를 만든다. 이것은 Rosen 교재에서 "이미 만든 알고리즘을 더 큰 알고리즘의 부품으로 사용한다"는 개념과 정확히 같다.

---

## 6A.3 **자연수**(Nat)의 구조 — 알고리즘의 기초

### Lean4에서 자연수는 어떻게 만들어져 있나?

Lean4에서 자연수(`Nat`)는 다음과 같이 정의되어 있다:

```lean
inductive Nat where
  | zero : Nat         -- 0이다
  | succ (n : Nat) : Nat  -- n의 다음 수이다
```

이 정의는 "자연수란 무엇인가?"를 **정확하게** 말해준다:

1. `zero`(0)는 자연수이다
2. 어떤 자연수 `n`이 있으면, `succ n`(n의 다음 수, 즉 n+1)도 자연수이다
3. 이 두 가지 방법으로만 자연수를 만들 수 있다

예를 들면:

| 수 | Lean4 표현 | 설명 |
|----|-----------|------|
| 0 | `Nat.zero` | 가장 작은 자연수 |
| 1 | `Nat.succ Nat.zero` | 0의 다음 수 |
| 2 | `Nat.succ (Nat.succ Nat.zero)` | 1의 다음 수 |
| 3 | `Nat.succ (Nat.succ (Nat.succ Nat.zero))` | 2의 다음 수 |

물론 Lean4에서 `0`, `1`, `2`, `3`이라고 그냥 써도 된다. 위의 표현은 내부적으로 이렇게 저장된다는 것을 보여주기 위한 것이다.

### 왜 이 구조가 중요한가?

이 구조가 중요한 이유는 **패턴 매칭**(pattern matching)과 **재귀**(recursion)의 기초가 되기 때문이다. 자연수에 대한 함수를 정의할 때, 두 가지 경우를 나눠서 처리할 수 있다:

```lean
-- 팩토리얼(계승) 함수: n! = 1 × 2 × ... × n
def fac : Nat → Nat
  | 0     => 1           -- 0! = 1 (기저 사례)
  | n + 1 => (n + 1) * fac n  -- (n+1)! = (n+1) × n! (재귀 사례)
```

이 정의를 자세히 분석해 보자:

**첫 번째 줄**: `def fac : Nat → Nat`
- `fac`이라는 이름의 함수를 정의한다
- `Nat → Nat`은 "자연수를 받아서 자연수를 돌려준다"는 뜻이다
- `:=` 대신 줄바꿈 후 `|`로 경우를 나누는 방식이다

**두 번째 줄**: `| 0 => 1`
- 입력이 0인 경우, 결과는 1이다 (0! = 1)
- 이것을 **기저 사례**(base case)라고 한다

**세 번째 줄**: `| n + 1 => (n + 1) * fac n`
- 입력이 n+1인 경우 (즉, 0이 아닌 경우)
- `(n + 1) * fac n`을 계산한다
- `fac n`은 **자기 자신을 다시 호출**한다 — 이것이 **재귀**(recursion)이다
- 이것을 **재귀 사례**(recursive case)라고 한다

### `#eval`로 팩토리얼 확인하기

```lean
#eval fac 0   -- 1
#eval fac 1   -- 1
#eval fac 2   -- 2
#eval fac 3   -- 6
#eval fac 4   -- 24
#eval fac 5   -- 120
#eval fac 10  -- 3628800
```

### 팩토리얼이 계산되는 과정

`fac 4`가 어떻게 계산되는지 단계별로 추적해 보자:

```
fac 4
= 4 * fac 3              -- n+1 = 4이므로 n = 3
= 4 * (3 * fac 2)        -- n+1 = 3이므로 n = 2
= 4 * (3 * (2 * fac 1))  -- n+1 = 2이므로 n = 1
= 4 * (3 * (2 * (1 * fac 0)))  -- n+1 = 1이므로 n = 0
= 4 * (3 * (2 * (1 * 1)))      -- fac 0 = 1 (기저 사례!)
= 4 * (3 * (2 * 1))
= 4 * (3 * 2)
= 4 * 6
= 24
```

핵심은 **재귀**가 결국 **기저 사례**(0)에 도달하여 멈춘다는 것이다. Lean4의 **종료 검사기**(termination checker)는 이 함수가 반드시 멈춘다는 것을 자동으로 확인한다. 매번 `fac n`을 호출할 때 `n`이 하나씩 줄어들기 때문이다.

---

## 6A.4 **리스트**(List)의 구조 — 알고리즘의 입력 자료구조

### Rosen 교재의 "수열"을 Lean4로 표현하기

Rosen 교재에서 알고리즘의 입력은 흔히 "정수의 수열 a₁, a₂, ..., aₙ"이다. Lean4에서 이것은 **리스트**(List)로 표현된다.

Lean4에서 리스트는 다음과 같이 정의되어 있다:

```lean
inductive List (α : Type) where
  | nil  : List α                  -- 빈 리스트
  | cons : α → List α → List α    -- 원소 하나를 앞에 붙이기
```

이 정의는 자연수의 정의와 매우 비슷하다:

| 자연수(Nat) | 리스트(List) | 비교 |
|-------------|-------------|------|
| `zero` (0) | `nil` (빈 리스트 `[]`) | 시작점 |
| `succ n` (n의 다음 수) | `cons a as` (리스트 as 앞에 a를 붙임) | 하나 더 추가 |

### Lean4에서 리스트 사용하기

```lean
-- 리스트를 만드는 여러 방법
#eval [1, 2, 3, 4, 5]           -- [1, 2, 3, 4, 5]
#eval ([] : List Nat)            -- [] (빈 리스트)
#eval 0 :: [1, 2, 3]            -- [0, 1, 2, 3] (앞에 붙이기)

-- 리스트의 기본 연산
#eval [1, 2, 3].length           -- 3 (길이)
#eval [1, 2, 3] ++ [4, 5]       -- [1, 2, 3, 4, 5] (이어붙이기)
#eval [1, 2, 3].reverse          -- [3, 2, 1] (뒤집기)
```

여기서 `::` 기호가 `cons`에 해당하고, `[]`가 `nil`에 해당한다. `[1, 2, 3]`은 `1 :: 2 :: 3 :: []`의 줄임 표현이다.

### 리스트에 대한 재귀 함수

리스트에 대해서도 자연수와 마찬가지로 재귀 함수를 정의할 수 있다:

```lean
-- 리스트의 모든 원소를 더하는 함수
def mySum : List Nat → Nat
  | []      => 0           -- 빈 리스트의 합은 0
  | a :: as => a + mySum as  -- 첫 원소 + 나머지 합

#eval mySum [1, 2, 3, 4, 5]  -- 15
#eval mySum []                -- 0
#eval mySum [10]              -- 10
```

이 함수가 어떻게 동작하는지 추적해 보자:

```
mySum [1, 2, 3]
= 1 + mySum [2, 3]       -- 첫 원소 1을 분리
= 1 + (2 + mySum [3])    -- 첫 원소 2를 분리
= 1 + (2 + (3 + mySum []))  -- 첫 원소 3을 분리
= 1 + (2 + (3 + 0))      -- 빈 리스트! 기저 사례
= 1 + (2 + 3)
= 1 + 5
= 6
```

---

## 6A.5 **최댓값 찾기** — 첫 번째 알고리즘 (Rosen 알고리즘 1)

### 교재의 의사 코드

Rosen 교재의 **알고리즘 1**은 "유한한 길이의 수열 중 가장 큰 값을 찾는 알고리즘"이다:

```
procedure max(a₁, a₂, ..., aₙ: integers)
max := a₁
for i := 2 to n
    if max < aᵢ then max := aᵢ
return max {max is the largest element}
```

이 알고리즘은 다음과 같이 동작한다:
1. 첫 번째 원소를 임시로 가장 큰 값(max)으로 설정한다
2. 나머지 원소를 차례대로 비교하여, 현재 max보다 크면 교체한다
3. 모든 원소를 확인한 후, max가 수열에서 가장 큰 값이다

### Lean4로 구현하기

Lean4에서는 리스트에 대한 **재귀**로 이 알고리즘을 표현한다:

```lean
-- 리스트에서 가장 큰 값을 찾는 함수
-- 빈 리스트의 경우 0을 반환한다고 약속한다
def findMax : List Nat → Nat
  | []      => 0                          -- 빈 리스트의 최댓값은 0
  | [a]     => a                          -- 원소가 하나뿐이면 그것이 최댓값
  | a :: as => if a ≥ findMax as           -- 첫 원소와 나머지의 최댓값을 비교
               then a
               else findMax as

#eval findMax [8, 4, 11, 3, 10]  -- 11
#eval findMax [1, 2, 3]          -- 3
#eval findMax [5, 5, 5]          -- 5
#eval findMax [42]               -- 42
```

또는 Lean4에 이미 있는 `List.maximum?`을 사용할 수도 있다:

```lean
#eval [8, 4, 11, 3, 10].maximum?  -- some 11
#eval ([] : List Nat).maximum?    -- none
```

`maximum?`이 `Option Nat`을 반환하는 이유는 빈 리스트에는 최댓값이 없기 때문이다. `some 11`은 "최댓값이 존재하며 그 값은 11이다"라는 뜻이고, `none`은 "최댓값이 존재하지 않는다"라는 뜻이다.

### 교재의 추적(Trace) 예시를 Lean4로

Rosen 교재에서는 입력 8, 4, 11, 3, 10에 대해 알고리즘을 추적한다. Lean4에서 이것을 단계별로 보려면:

```
findMax [8, 4, 11, 3, 10]
  -- 첫 원소 8과 findMax [4, 11, 3, 10]을 비교
  
findMax [4, 11, 3, 10]
  -- 첫 원소 4와 findMax [11, 3, 10]을 비교
  
findMax [11, 3, 10]
  -- 첫 원소 11과 findMax [3, 10]을 비교
  
findMax [3, 10]
  -- 첫 원소 3과 findMax [10]을 비교
  
findMax [10]
  -- 원소가 하나 → 10 반환

findMax [3, 10] = max(3, 10) = 10
findMax [11, 3, 10] = max(11, 10) = 11
findMax [4, 11, 3, 10] = max(4, 11) = 11
findMax [8, 4, 11, 3, 10] = max(8, 11) = 11
```

최종 결과는 **11**이다. 교재의 추적 결과와 동일하다.

---

## 6A.6 연습문제 세트 1: 기본 함수 정의

### 연습 1-1: 절댓값 함수 (괄호 채우기)

다음 함수는 정수의 절댓값을 계산한다. 빈칸을 채워라.

```lean
def myAbs (n : Int) : Int :=
  if n ≥ 0 then (______) else (______)
```

<details>
<summary>💡 답 보기</summary>

```lean
def myAbs (n : Int) : Int :=
  if n ≥ 0 then n else (-n)
```

**설명**: `n`이 0 이상이면 `n` 자체가 절댓값이다. `n`이 음수이면 `-n`(부호를 바꾼 것)이 절댓값이다.

`#eval myAbs (-5)`로 결과가 `5`인지 확인할 수 있다.

</details>

---

### 연습 1-2: 최솟값 함수 (괄호 채우기)

두 자연수 중 더 작은 것을 반환하는 함수를 완성하라.

```lean
def myMin (a : Nat) (b : Nat) : Nat :=
  if (______) then a else b
```

<details>
<summary>💡 답 보기</summary>

```lean
def myMin (a : Nat) (b : Nat) : Nat :=
  if a ≤ b then a else b
```

**설명**: `a`가 `b`보다 작거나 같으면 `a`가 최솟값이고, 그렇지 않으면 `b`가 최솟값이다.

테스트:
```lean
#eval myMin 3 7  -- 3
#eval myMin 9 2  -- 2
#eval myMin 5 5  -- 5
```

</details>

---

### 연습 1-3: 팩토리얼 (sorry 채우기)

팩토리얼 함수를 완성하라.

```lean
def myFac : Nat → Nat
  | 0     => sorry
  | n + 1 => sorry
```

<details>
<summary>💡 답 보기</summary>

```lean
def myFac : Nat → Nat
  | 0     => 1
  | n + 1 => (n + 1) * myFac n
```

**설명**:
- 0! = 1 (수학적 정의)
- (n+1)! = (n+1) × n! (재귀적 정의)

테스트:
```lean
#eval myFac 5   -- 120
#eval myFac 10  -- 3628800
```

</details>

---

### 연습 1-4: 리스트 합 함수 (sorry 채우기)

리스트의 모든 원소를 더하는 함수를 완성하라.

```lean
def listSum : List Nat → Nat
  | []      => sorry
  | a :: as => sorry
```

<details>
<summary>💡 답 보기</summary>

```lean
def listSum : List Nat → Nat
  | []      => 0
  | a :: as => a + listSum as
```

**설명**:
- 빈 리스트의 합은 0이다 (아무것도 없으니까)
- 비어있지 않은 리스트는 첫 원소 `a`와 나머지 리스트 `as`의 합을 더한다

테스트:
```lean
#eval listSum [1, 2, 3, 4, 5]  -- 15
#eval listSum []                -- 0
```

</details>

---

### 연습 1-5: 리스트 길이 함수 (sorry 채우기)

리스트의 원소 개수를 세는 함수를 완성하라.

```lean
def myLength : List Nat → Nat
  | []      => sorry
  | _ :: as => sorry
```

여기서 `_`는 "이 값을 사용하지 않겠다"는 뜻이다. 길이를 셀 때 원소의 **값**은 중요하지 않고, **개수**만 중요하기 때문이다.

<details>
<summary>💡 답 보기</summary>

```lean
def myLength : List Nat → Nat
  | []      => 0
  | _ :: as => 1 + myLength as
```

**설명**:
- 빈 리스트의 길이는 0이다
- 비어있지 않은 리스트의 길이는 1 + 나머지 리스트의 길이이다

테스트:
```lean
#eval myLength [1, 2, 3]  -- 3
#eval myLength []          -- 0
#eval myLength [42]        -- 1
```

</details>

---

### 연습 1-6: 거듭제곱 함수 (전체 작성)

자연수 `b`의 `n`제곱을 계산하는 함수 `myPow`를 직접 작성하라. 패턴 매칭과 재귀를 사용하라.

힌트: b⁰ = 1, bⁿ⁺¹ = b × bⁿ

```lean
def myPow : Nat → Nat → Nat
  | _, 0     => sorry
  | b, n + 1 => sorry
```

<details>
<summary>💡 답 보기</summary>

```lean
def myPow : Nat → Nat → Nat
  | _, 0     => 1
  | b, n + 1 => b * myPow b n
```

**설명**:
- 어떤 수의 0제곱이든 1이다 (b⁰ = 1)
- bⁿ⁺¹ = b × bⁿ (재귀적 정의)

테스트:
```lean
#eval myPow 2 10  -- 1024
#eval myPow 3 4   -- 81
#eval myPow 5 0   -- 1
```

</details>

---

## 6A.7 **선형 탐색**(Linear Search) — Rosen 알고리즘 2

### 교재의 의사 코드

Rosen 교재의 **알고리즘 2**는 선형 탐색이다:

```
procedure linear search(x: integer, a₁, a₂, ..., aₙ: distinct integers)
i := 1
while (i ≤ n and x ≠ aᵢ)
    i := i + 1
if i ≤ n then location := i
else location := 0
return location
```

이 알고리즘은 리스트에서 특정 값 `x`를 찾아서:
- 찾으면 그 **위치**(1부터 시작)를 반환한다
- 찾지 못하면 0을 반환한다

### Lean4로 구현하기 — 버전 1 (Bool 반환)

먼저 가장 간단한 버전부터 만들자. 값이 리스트에 **있는지 없는지**만 판단한다:

```lean
-- 리스트에 특정 값이 있는지 확인
def contains : Nat → List Nat → Bool
  | _, []      => false                    -- 빈 리스트에는 아무것도 없다
  | x, a :: as => if x == a then true      -- 첫 원소와 같으면 찾았다!
                  else contains x as       -- 아니면 나머지에서 계속 찾는다

#eval contains 5 [1, 2, 3, 4, 5]   -- true
#eval contains 7 [1, 2, 3, 4, 5]   -- false
#eval contains 1 [1, 1, 1]         -- true
#eval contains 0 []                 -- false
```

이 함수의 동작을 추적해 보자. `contains 3 [1, 2, 3, 4]`의 경우:

```
contains 3 [1, 2, 3, 4]
  3 == 1? 아니다 → contains 3 [2, 3, 4]
  3 == 2? 아니다 → contains 3 [3, 4]
  3 == 3? 맞다! → true
```

`contains 7 [1, 2, 3]`의 경우:

```
contains 7 [1, 2, 3]
  7 == 1? 아니다 → contains 7 [2, 3]
  7 == 2? 아니다 → contains 7 [3]
  7 == 3? 아니다 → contains 7 []
  빈 리스트 → false
```

### Lean4로 구현하기 — 버전 2 (위치 반환)

이제 교재처럼 위치를 반환하는 버전을 만들자. 단, Lean4에서는 `Option Nat`을 사용한다:

```lean
-- 리스트에서 값을 찾아 위치(0부터 시작)를 반환
-- 없으면 none을 반환
def linearSearch : Nat → List Nat → Option Nat
  | _, []      => none                         -- 빈 리스트 → 못 찾음
  | x, a :: as => if x == a then some 0        -- 찾았다! 위치는 0
                  else match linearSearch x as with
                       | none   => none          -- 나머지에서도 못 찾음
                       | some i => some (i + 1)  -- 나머지에서 i번째에서 찾음
                                                  -- → 전체에서는 i+1번째

#eval linearSearch 19 [1, 2, 3, 5, 6, 7, 8, 10, 12, 13, 15, 16, 18, 19, 20, 22]
-- some 13 (0부터 세서 13번째, 즉 14번째 원소)

#eval linearSearch 99 [1, 2, 3]  -- none
```

### `Option` 타입이 뭔가?

`Option`은 "결과가 있을 수도 있고 없을 수도 있다"를 표현하는 타입이다:

```lean
inductive Option (α : Type) where
  | none : Option α        -- 결과 없음
  | some : α → Option α    -- 결과 있음, 값은 α
```

이것은 교재에서 "찾지 못하면 0을 반환"하는 것보다 더 **정확한** 표현이다. 왜냐하면 교재의 방식에서는 "위치가 0"인 것과 "찾지 못했음"을 구별할 수 없기 때문이다. (물론 교재에서는 위치를 1부터 세기 때문에 문제가 되지 않지만, 프로그래밍에서는 0부터 세는 것이 일반적이다.)

---

## 6A.8 연습문제 세트 2: 탐색과 리스트 함수

### 연습 2-1: 음수의 개수 세기 (괄호 채우기)

정수 리스트에서 음수의 개수를 세는 함수를 완성하라.

```lean
def countNeg : List Int → Nat
  | []      => (______)
  | a :: as => if a < 0 then (______) else (______)
```

<details>
<summary>💡 답 보기</summary>

```lean
def countNeg : List Int → Nat
  | []      => 0
  | a :: as => if a < 0 then 1 + countNeg as else countNeg as
```

**설명**:
- 빈 리스트에는 음수가 0개이다
- 첫 원소가 음수이면 1을 더하고 나머지를 센다
- 첫 원소가 음수가 아니면 나머지만 센다

테스트:
```lean
#eval countNeg [-3, 2, -1, 0, 5, -7]  -- 3
#eval countNeg [1, 2, 3]               -- 0
#eval countNeg []                       -- 0
```

</details>

---

### 연습 2-2: 짝수만 걸러내기 (sorry 채우기)

자연수 리스트에서 짝수만 남기는 함수를 완성하라.

```lean
def filterEven : List Nat → List Nat
  | []      => sorry
  | a :: as => sorry
```

힌트: `a % 2 == 0`으로 짝수인지 판단할 수 있다.

<details>
<summary>💡 답 보기</summary>

```lean
def filterEven : List Nat → List Nat
  | []      => []
  | a :: as => if a % 2 == 0 then a :: filterEven as
               else filterEven as
```

**설명**:
- 빈 리스트를 걸러내면 빈 리스트이다
- 첫 원소가 짝수이면 결과에 포함하고 나머지를 계속 걸러낸다
- 첫 원소가 홀수이면 건너뛰고 나머지를 계속 걸러낸다

테스트:
```lean
#eval filterEven [1, 2, 3, 4, 5, 6]  -- [2, 4, 6]
#eval filterEven [1, 3, 5]            -- []
#eval filterEven [2, 4, 6]            -- [2, 4, 6]
```

</details>

---

### 연습 2-3: 마지막으로 나온 짝수의 위치 (Rosen 연습문제 7)

Rosen 교재 연습문제 7번: "n개의 정수로 된 리스트를 입력으로 받고, 짝수가 가장 마지막으로 나오는 위치를 출력하라. 짝수가 없으면 0을 출력하라."

이것을 Lean4로 구현하라.

```lean
-- 짝수의 마지막 위치 찾기 (1부터 세기)
-- 보조 함수: 현재 위치를 추적하면서 마지막 짝수 위치를 기록
def lastEvenPos : List Nat → Nat :=
  sorry
```

<details>
<summary>💡 답 보기</summary>

```lean
-- 보조 함수: 현재 인덱스와 마지막으로 찾은 짝수 위치를 추적
def lastEvenPosAux : List Nat → Nat → Nat → Nat
  | [], _, lastPos       => lastPos
  | a :: as, idx, lastPos =>
      if a % 2 == 0 then lastEvenPosAux as (idx + 1) idx
      else lastEvenPosAux as (idx + 1) lastPos

def lastEvenPos (xs : List Nat) : Nat :=
  lastEvenPosAux xs 1 0

#eval lastEvenPos [1, 2, 3, 4, 5]    -- 4 (4가 위치 4에 있다)
#eval lastEvenPos [2, 4, 6, 8]       -- 4 (8이 위치 4에 있다)
#eval lastEvenPos [1, 3, 5, 7]       -- 0 (짝수 없음)
```

**설명**: 보조 함수 `lastEvenPosAux`는 세 가지 정보를 가지고 리스트를 순회한다:
- 남은 리스트
- 현재 보고 있는 위치 (`idx`)
- 마지막으로 발견한 짝수의 위치 (`lastPos`)

짝수를 발견할 때마다 `lastPos`를 현재 `idx`로 갱신한다. 이것은 Rosen 교재의 의사 코드에서 "for 루프를 돌면서 변수를 갱신"하는 것과 같은 패턴이다. Lean4에서는 "변수를 갱신"하는 대신 "새로운 값을 재귀 호출에 전달"한다.

</details>

---

### 연습 2-4: 회문 판별 (Rosen 연습문제 9)

Rosen 교재 연습문제 9번: "n 글자로 이루어진 문자열이 **회문**(palindrome)인지 아닌지 판단하는 알고리즘을 구하라."

**회문**이란 앞에서 읽으나 뒤에서 읽으나 같은 문자열이다. 예: "토마토", "12321"

자연수 리스트 버전으로 구현하라.

```lean
def isPalindrome (xs : List Nat) : Bool :=
  sorry
```

힌트: 리스트를 뒤집어서 원래와 같은지 비교하면 된다.

<details>
<summary>💡 답 보기</summary>

```lean
-- 두 리스트가 같은지 비교
def listEqual : List Nat → List Nat → Bool
  | [], []           => true
  | a :: as, b :: bs => a == b && listEqual as bs
  | _, _             => false

def isPalindrome (xs : List Nat) : Bool :=
  listEqual xs xs.reverse

#eval isPalindrome [1, 2, 3, 2, 1]  -- true
#eval isPalindrome [1, 2, 3]         -- false
#eval isPalindrome [1]               -- true
#eval isPalindrome []                 -- true
```

사실 Lean4에서는 `BEq` 인스턴스가 있으므로 더 간단하게 쓸 수 있다:

```lean
def isPalindrome' (xs : List Nat) : Bool :=
  xs == xs.reverse
```

</details>

---

## 6A.9 **정리**(Theorem)로 알고리즘 검증하기 — 정확성 증명

### 왜 알고리즘을 "증명"해야 하나?

Rosen 교재에서 알고리즘의 **정확성**(correctness)은 매우 중요한 속성이다. 교재에서는 알고리즘 1(최댓값 찾기)이 정확하다는 것을 다음과 같이 설명한다:

> "이 알고리즘이 정확하다는 것을 보이려면, 알고리즘이 종료했을 때 max의 값이 수열의 가장 큰 값이라는 것을 보이면 된다."

Lean4에서는 이 정확성을 **정리**(theorem)로 표현하고 **증명**할 수 있다. 이것이 Lean4의 가장 강력한 특징이다 — 알고리즘을 작성할 뿐만 아니라, 그 알고리즘이 **올바르게** 작동한다는 것을 수학적으로 증명할 수 있다.

### 간단한 예시: myAdd의 정확성

```lean
-- myAdd가 교환법칙을 만족한다는 정리
theorem myAdd_comm (a b : Nat) : myAdd a b = myAdd b a := by
  -- myAdd의 정의를 펼친다
  simp [myAdd]
  -- Nat의 덧셈에 대한 교환법칙 적용
  omega
```

여기서 일어나는 일을 단계별로 보면:

1. `simp [myAdd]` — `myAdd`의 정의(`a + b`)를 풀어쓴다
2. `omega` — 자연수 덧셈에 대한 교환법칙(`a + b = b + a`)을 자동으로 증명한다

### 보조정리(lemma)와 정리(theorem)의 관계 복습

Part 5에서 배운 내용을 복습하자. Lean4에서 `theorem`과 `lemma`는 **기능적으로 동일**하다. 둘 다 수학적 사실을 증명한다. 관례적으로:

| 이름 | 역할 | 비유 |
|------|------|------|
| `lemma`(보조정리) | 더 큰 증명을 위한 중간 단계 | 건물의 벽돌 |
| `theorem`(정리) | 최종적으로 보이고 싶은 결과 | 건물 전체 |

알고리즘 정확성 증명에서 이것이 어떻게 나타나는지 보자:

```lean
-- 보조정리: 리스트가 비어있지 않으면 mySum은 0보다 크거나 같다
lemma mySum_nonneg (xs : List Nat) : 0 ≤ mySum xs := by
  induction xs with
  | nil => simp [mySum]
  | cons a as ih => simp [mySum]; omega

-- 정리: mySum [a] = a (원소가 하나인 리스트의 합은 그 원소 자체)
theorem mySum_singleton (a : Nat) : mySum [a] = a := by
  simp [mySum]
```

여기서 `lemma mySum_nonneg`은 나중에 더 복잡한 증명에서 사용될 수 있는 **보조 사실**이고, `theorem mySum_singleton`은 우리가 직접 확인하고 싶은 **주요 결과**이다.

---

## 6A.10 연습문제 세트 3: 간단한 증명

### 연습 3-1: myMax의 기본 성질 (괄호 채우기)

`myMax a a = a`임을 증명하라.

```lean
theorem myMax_self (a : Nat) : myMax a a = a := by
  simp [myMax]
  (______)
```

<details>
<summary>💡 답 보기</summary>

```lean
theorem myMax_self (a : Nat) : myMax a a = a := by
  simp [myMax]
```

**설명**: `myMax a a`의 정의를 펼치면 `if a ≥ a then a else a`가 된다. `a ≥ a`는 항상 참이므로 결과는 `a`이다. `simp`가 이것을 자동으로 처리한다.

</details>

---

### 연습 3-2: myLength의 성질 (sorry 채우기)

빈 리스트의 길이가 0임을 증명하라.

```lean
theorem myLength_nil : myLength ([] : List Nat) = 0 := by
  sorry
```

<details>
<summary>💡 답 보기</summary>

```lean
theorem myLength_nil : myLength ([] : List Nat) = 0 := by
  rfl
```

**설명**: `myLength []`는 정의에 의해 `0`이다. 정의를 펼치면 양변이 동일하므로 `rfl`(reflexivity, 반사성)로 충분하다. `rfl`은 "양변이 정의적으로 같다"를 표현한다.

</details>

---

### 연습 3-3: 팩토리얼의 기본 성질

`fac 1 = 1`임을 증명하라.

```lean
theorem fac_one : fac 1 = 1 := by
  sorry
```

<details>
<summary>💡 답 보기</summary>

```lean
theorem fac_one : fac 1 = 1 := by
  rfl
```

또는:

```lean
theorem fac_one : fac 1 = 1 := by
  simp [fac]
```

**설명**: `fac 1 = fac (0 + 1) = (0 + 1) * fac 0 = 1 * 1 = 1`. 이 계산을 Lean4가 자동으로 수행하여 양변이 같다고 판단한다.

</details>

---

### 연습 3-4: contains의 성질

어떤 원소 `a`가 `[a]`(원소가 하나인 리스트)에 포함되어 있음을 증명하라.

```lean
theorem contains_singleton (a : Nat) : contains a [a] = true := by
  sorry
```

<details>
<summary>💡 답 보기</summary>

```lean
theorem contains_singleton (a : Nat) : contains a [a] = true := by
  simp [contains]
```

**설명**: `contains a [a]`를 정의에 따라 풀면:
- 리스트가 `a :: []`이다
- `a == a`를 확인하면 `true`이다
- 따라서 결과는 `true`이다

`simp [contains]`가 이 정의를 자동으로 풀어서 확인한다.

</details>

---

## 6A.11 Rosen 교재 연습문제 1번을 Lean4로

### 문제

> 알고리즘 1이 리스트 1, 8, 12, 9, 11, 2, 14, 5, 10, 4에서 최댓값을 찾는 모든 과정을 나열하라.

### Lean4 풀이

교재의 추적을 Lean4의 `#eval`로 확인할 수 있다:

```lean
-- 교재 연습문제 1: 알고리즘 1의 추적
#eval findMax [1, 8, 12, 9, 11, 2, 14, 5, 10, 4]  -- 14
```

교재 스타일의 추적을 보여주기 위해, 각 단계에서의 임시 최댓값을 기록하는 함수를 만들 수 있다:

```lean
-- 추적 버전: 각 단계에서의 max 값을 기록
def findMaxTrace : List Nat → List Nat
  | []      => []
  | [a]     => [a]
  | a :: as =>
    let restMax := findMax as
    let currentMax := if a ≥ restMax then a else restMax
    currentMax :: findMaxTrace as

#eval findMaxTrace [1, 8, 12, 9, 11, 2, 14, 5, 10, 4]
-- [14, 14, 14, 14, 14, 14, 14, 10, 10, 4]
```

교재의 풀이 방식대로 설명하면:
1. max = 1 (첫 번째 원소)
2. 8과 비교: 8 > 1 → max = 8
3. 12와 비교: 12 > 8 → max = 12
4. 9와 비교: 9 < 12 → max = 12 (변화 없음)
5. 11과 비교: 11 < 12 → max = 12 (변화 없음)
6. 2와 비교: 2 < 12 → max = 12 (변화 없음)
7. 14와 비교: 14 > 12 → max = 14
8. 5와 비교: 5 < 14 → max = 14 (변화 없음)
9. 10과 비교: 10 < 14 → max = 14 (변화 없음)
10. 4와 비교: 4 < 14 → max = 14 (변화 없음)

최종 결과: **14**

---

## 6A.12 **`if`(→)와 `if and only if`(↔)의 차이** — 알고리즘 조건과 동치

### 왜 여기서 이 개념이 필요한가?

알고리즘의 정확성을 증명할 때, 다음과 같은 문장이 자주 등장한다:

- "x가 리스트에 **있으면**, `contains x xs = true`이다" (→, if)
- "`contains x xs = true`인 것은 x가 리스트에 **있는 것과 같다**" (↔, if and only if)

이 둘의 차이를 정확히 이해하는 것이 중요하다.

### `→`(if, 조건문) — 한 방향 화살표

`P → Q`는 "P이면 Q이다"라는 뜻이다. 한 방향으로만 성립한다.

Lean4에서 이것은 **함수**와 같다. P라는 증거를 받아서 Q라는 증거를 만들어내는 함수이다.

```lean
-- P → Q의 예시: "n이 짝수이면, 2*n은 4의 배수이다"
-- 이것은 한 방향으로만 성립한다!
-- 역방향 "2*n이 4의 배수이면 n은 짝수이다"는 별도로 증명해야 한다

example (n : Nat) (h : n % 2 = 0) : (2 * n) % 4 = 0 := by
  omega
```

### `↔`(if and only if, 동치) — 양방향 화살표

`P ↔ Q`는 "P이면 Q이고, Q이면 P이다"라는 뜻이다. **양방향** 모두 성립한다.

이것은 `(P → Q) ∧ (Q → P)`와 같다. 즉, 두 개의 `→`를 합친 것이다.

```lean
-- P ↔ Q의 예시
-- "n은 짝수이다" ↔ "n을 2로 나눈 나머지가 0이다"
-- 양방향 모두 성립한다!
```

### 비유로 이해하기

| 기호 | 읽는 법 | 비유 | 의미 |
|------|--------|------|------|
| `→` | "이면" (if) | 일방통행 도로 | A에서 B로만 갈 수 있다 |
| `↔` | "인 것과 같다" (if and only if) | 양방향 도로 | A에서 B로, B에서 A로 모두 갈 수 있다 |

### Lean4에서 `↔` 사용하기

```lean
-- ↔를 증명하려면 constructor를 사용하여 양방향을 각각 증명한다
example (n : Nat) : n = 0 ↔ n + 1 = 1 := by
  constructor        -- 두 방향으로 나눈다
  · intro h          -- 방향 1: n = 0 → n + 1 = 1
    rw [h]           -- n을 0으로 치환
  · intro h          -- 방향 2: n + 1 = 1 → n = 0
    omega            -- 산술적으로 자명
```

이 증명의 구조를 자세히 보면:

1. `constructor` — 목표 `P ↔ Q`를 두 개의 하위 목표 `P → Q`와 `Q → P`로 나눈다
2. 첫 번째 `·` 블록 — `P → Q` 방향을 증명한다
3. 두 번째 `·` 블록 — `Q → P` 방향을 증명한다

### `↔`의 두 방향을 사용하기

이미 증명된 `↔`를 사용할 때는 `.mp`(정방향)와 `.mpr`(역방향)으로 원하는 방향을 꺼낸다:

```lean
-- h : P ↔ Q가 있을 때
-- h.mp  : P → Q  (정방향, "modus ponens")
-- h.mpr : Q → P  (역방향, "modus ponens reverse")

example (h : n = 0 ↔ n + 1 = 1) (h2 : n = 0) : n + 1 = 1 :=
  h.mp h2    -- 정방향 사용

example (h : n = 0 ↔ n + 1 = 1) (h2 : n + 1 = 1) : n = 0 :=
  h.mpr h2   -- 역방향 사용
```

### `rw`로 `↔` 사용하기

`↔`는 `rw` 전술과 함께 사용할 수도 있다. 이것이 매우 편리한 기능이다:

```lean
-- ↔를 rw로 사용하는 예시
-- abs_lt : |x| < y ↔ -y < x ∧ x < y

example (x : ℝ) (h : |x + 3| < 5) : -8 < x ∧ x < 2 := by
  rw [abs_lt] at h    -- h를 ↔의 우변으로 치환
  constructor <;> linarith
```

---

## 6A.13 연습문제 세트 4: `→`와 `↔`

### 연습 4-1: `→` 증명 (괄호 채우기)

"리스트가 비어있으면 그 길이는 0이다"를 증명하라.

```lean
theorem empty_has_zero_length (xs : List Nat) (h : xs = []) : xs.length = 0 := by
  rw [(______)]
```

<details>
<summary>💡 답 보기</summary>

```lean
theorem empty_has_zero_length (xs : List Nat) (h : xs = []) : xs.length = 0 := by
  rw [h]
```

**설명**: 가설 `h : xs = []`을 `rw [h]`로 사용하면, 목표의 `xs`가 `[]`로 치환되어 `[].length = 0`이 된다. 이것은 정의에 의해 참이므로 자동으로 증명이 완료된다.

</details>

---

### 연습 4-2: `↔` 증명 (sorry 채우기)

다음 동치를 증명하라.

```lean
theorem add_eq_zero_iff (a b : Nat) : a + b = 0 ↔ a = 0 ∧ b = 0 := by
  constructor
  · sorry  -- 정방향: a + b = 0 → a = 0 ∧ b = 0
  · sorry  -- 역방향: a = 0 ∧ b = 0 → a + b = 0
```

<details>
<summary>💡 답 보기</summary>

```lean
theorem add_eq_zero_iff (a b : Nat) : a + b = 0 ↔ a = 0 ∧ b = 0 := by
  constructor
  · intro h
    constructor
    · omega
    · omega
  · intro ⟨ha, hb⟩
    rw [ha, hb]
```

**설명**:
- 정방향: `a + b = 0`이면 자연수에서 `a`와 `b` 모두 0이어야 한다. `omega`가 이를 자동으로 증명한다.
- 역방향: `a = 0`이고 `b = 0`이면, `a + b = 0 + 0 = 0`이다. `rw`로 치환하면 `0 = 0`이 되어 자명하다.

</details>

---

### 연습 4-3: `→`와 `↔`의 차이 이해하기

다음 중 `↔`가 성립하는 것과 `→`만 성립하는 것을 구분하라.

(a) "n이 4의 배수이면, n은 2의 배수이다"

```lean
-- 이것은 → (한 방향만 성립)
-- 역방향: "n이 2의 배수이면 n은 4의 배수이다"는 거짓 (반례: n = 6)
example (n : Nat) (h : 4 ∣ n) : 2 ∣ n := by
  sorry
```

(b) "n이 짝수인 것은 n²이 짝수인 것과 같다"

```lean
-- 이것은 ↔ (양방향 성립)
-- 짝수의 제곱은 짝수이고, 제곱이 짝수이면 원래 수도 짝수이다
```

<details>
<summary>💡 답 보기</summary>

(a) `→`만 성립:

```lean
example (n : Nat) (h : 4 ∣ n) : 2 ∣ n := by
  obtain ⟨k, hk⟩ := h     -- h : 4 ∣ n을 n = 4 * k로 분해
  use 2 * k                -- n = 2 * (2 * k)임을 보인다
  omega
```

반례: n = 6은 2의 배수이지만 4의 배수가 아니다. 따라서 역방향은 성립하지 않고, `↔`는 아니다.

(b) `↔` 성립: 이 증명은 상당히 복잡하므로 여기서는 개념만 이해하면 된다.

</details>

---

## 6A.14 **치환/대입**(Substitution) 복습 — `rw`의 본질

### 치환이란?

**치환**(substitution)은 "같은 것은 같은 것으로 바꿔도 된다"는 원리이다. 수학에서 가장 기본적이면서도 가장 중요한 원리 중 하나이다.

예를 들어, `a = 5`라는 사실이 있으면, `a + 3`을 `5 + 3`으로 바꿀 수 있다. 이것이 치환이다.

Lean4에서 치환은 `rw` 전술로 수행된다:

```lean
-- rw 전술의 기본 사용법
example (a b c : Nat) (h : a = b) : a + c = b + c := by
  rw [h]    -- a를 b로 치환 → 목표가 b + c = b + c가 됨 → 자동 완료
```

### `rw`의 네 가지 패턴

```lean
-- 1. 기본 치환: h의 좌변 → 우변
-- h : a = b일 때, rw [h]는 목표의 a를 b로 바꾼다
example (a b : Nat) (h : a = b) : a + a = b + b := by
  rw [h]

-- 2. 역방향 치환: h의 우변 → 좌변  
-- ← 기호를 사용한다
example (a b : Nat) (h : a = b) : b + b = a + a := by
  rw [← h]

-- 3. 가설에서 치환: 목표가 아니라 가설을 변경
-- at 키워드를 사용한다
example (a b c : Nat) (h1 : a = b) (h2 : a + c = 10) : b + c = 10 := by
  rw [h1] at h2    -- h2의 a를 b로 치환
  exact h2

-- 4. 연속 치환: 여러 개를 한 번에
example (a b c : Nat) (h1 : a = b) (h2 : b = c) : a = c := by
  rw [h1, h2]    -- 먼저 a→b, 그 다음 b→c
```

### 치환과 알고리즘

알고리즘의 정확성을 증명할 때, 치환은 핵심적인 역할을 한다:

```lean
-- findMax의 정확성 증명에서 치환 사용
-- "findMax [a]는 a와 같다"
theorem findMax_singleton (a : Nat) : findMax [a] = a := by
  rfl  -- 정의에 의해 같다 (치환 불필요)

-- "findMax [a, b]는 max(a, b)와 같다"
theorem findMax_pair (a b : Nat) : findMax [a, b] = if a ≥ b then a else b := by
  simp [findMax]
```

---

## 6A.15 전술 요약표 (Part 6-A까지)

### 이 파트에서 새로 배운 것

| 개념 | Lean4 표현 | 설명 |
|------|-----------|------|
| 함수 정의 | `def f (x : α) : β := ...` | 알고리즘을 정의한다 |
| 패턴 매칭 | `\| pattern => result` | 입력의 형태에 따라 다른 처리 |
| 재귀 | 함수 본문에서 자기 자신 호출 | 루프 대신 사용 |
| `#eval` | `#eval f args` | 함수를 실행하여 결과 확인 |
| `Option` | `some v` / `none` | 결과가 있을 수도 없을 수도 있음 |

### 이전 파트에서 배운 전술 (복습)

| 전술 | 용도 | 예시 |
|------|------|------|
| `rfl` | 양변이 정의적으로 같을 때 | `example : 1 + 1 = 2 := by rfl` |
| `rw [h]` | h로 치환 | `rw [mul_comm]` |
| `rw [← h]` | h의 역방향 치환 | `rw [← add_assoc]` |
| `simp` | 자동 단순화 | `simp [myFunc]` |
| `omega` | 자연수/정수 산술 | 등식·부등식 자동 증명 |
| `intro` | 가정 도입 | `intro h` |
| `exact` | 정확히 일치하는 증거 | `exact h` |
| `apply` | 결론이 매칭되는 정리 적용 | `apply Nat.le_add_right` |
| `constructor` | `∧`나 `↔`를 분리 | 두 개의 하위 목표 생성 |
| `cases` | 경우 분해 | `cases h with \| ...` |

---

## 6A.16 도전 문제

### 도전 1: 리스트 뒤집기 함수 구현

리스트를 뒤집는 함수 `myReverse`를 구현하라. 이어붙이기(`++`)를 사용해도 된다.

```lean
def myReverse : List Nat → List Nat
  | []      => sorry
  | a :: as => sorry
```

<details>
<summary>💡 답 보기</summary>

```lean
def myReverse : List Nat → List Nat
  | []      => []
  | a :: as => myReverse as ++ [a]

#eval myReverse [1, 2, 3, 4, 5]  -- [5, 4, 3, 2, 1]
```

**설명**: 첫 원소 `a`를 분리하고, 나머지 `as`를 먼저 뒤집은 다음, `a`를 맨 뒤에 붙인다.

예: `myReverse [1, 2, 3]`
= `myReverse [2, 3] ++ [1]`
= `(myReverse [3] ++ [2]) ++ [1]`
= `((myReverse [] ++ [3]) ++ [2]) ++ [1]`
= `(([] ++ [3]) ++ [2]) ++ [1]`
= `([3] ++ [2]) ++ [1]`
= `[3, 2] ++ [1]`
= `[3, 2, 1]`

</details>

---

### 도전 2: 두 변수의 값 교환 (Rosen 연습문제 11)

Rosen 교재 연습문제 11번: "대입문만을 이용해서 두 변수 x와 y의 값을 교환하는 알고리즘을 구하라."

Lean4에서는 "변수를 교환"하는 대신, **순서쌍**(pair)을 뒤집는 함수로 표현한다:

```lean
-- 순서쌍의 두 원소를 교환하는 함수
def swap (p : Nat × Nat) : Nat × Nat :=
  sorry

#eval swap (3, 7)  -- 기대 결과: (7, 3)
```

<details>
<summary>💡 답 보기</summary>

```lean
def swap (p : Nat × Nat) : Nat × Nat :=
  (p.2, p.1)

#eval swap (3, 7)  -- (7, 3)
```

그리고 교환의 정확성을 증명할 수도 있다:

```lean
-- swap을 두 번 하면 원래대로 돌아온다
theorem swap_swap (p : Nat × Nat) : swap (swap p) = p := by
  simp [swap]
```

</details>

---

### 도전 3: 리스트에 포함된 모든 정수의 합 (Rosen 연습문제 3)

Rosen 교재 연습문제 3번: "리스트에 포함된 모든 정수의 합을 구하는 알고리즘을 구하라."

이것은 이미 `mySum`으로 구현했다. 추가로, **정확성**을 간단하게 증명해 보자:

```lean
-- mySum의 기본 성질: 두 리스트를 이어붙인 것의 합 = 각각의 합의 합
theorem mySum_append (xs ys : List Nat) :
  mySum (xs ++ ys) = mySum xs + mySum ys := by
  sorry
```

<details>
<summary>💡 답 보기</summary>

```lean
theorem mySum_append (xs ys : List Nat) :
  mySum (xs ++ ys) = mySum xs + mySum ys := by
  induction xs with
  | nil => simp [mySum]
  | cons a as ih =>
    simp [mySum]
    rw [ih]
    omega
```

**설명**: 리스트 `xs`에 대한 귀납법을 사용한다.
- 기저 사례: `xs = []`이면 `mySum ([] ++ ys) = mySum ys = 0 + mySum ys = mySum [] + mySum ys`
- 귀납 단계: `xs = a :: as`이면, 귀납 가정 `mySum (as ++ ys) = mySum as + mySum ys`를 사용하여 `mySum ((a :: as) ++ ys) = a + mySum (as ++ ys) = a + mySum as + mySum ys = mySum (a :: as) + mySum ys`

</details>

---

**(Part 6-A 끝 — Part 6-B에서 이진 탐색, 정렬, 문자열 매칭을 학습한다)**
