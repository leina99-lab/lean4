# Part 15-B: 유한상태 기계 — 출력이 있는 기계와 결정적 오토마톤

> **Rosen 이산수학 8판 · Chapter 13 (Section 13.2~13.3 전반) 기반**
> **Lean 4 형식화 + 3단계 연습문제**

---

## 0. 들어가며

Part 15-A에서 문법(grammar)으로 언어를 **생성**하는 방법을 배웠다. 이번 Part에서는 반대로, 주어진 문자열이 특정 언어에 **속하는지 판단**하는 **유한상태 기계**(finite-state machine, FSM)를 배운다.

유한상태 기계는 컴파일러의 어휘 분석기, 정규 표현식 엔진, 네트워크 프로토콜, 디지털 회로 등 **어디에나** 쓰인다.

---

## 1. 출력이 있는 유한상태 기계 — 밀리 기계

### 1.1 직관: 자동판매기

유한상태 기계를 이해하는 가장 좋은 비유는 **자동판매기**이다.

- **상태**: 지금까지 투입된 금액 (0원, 500원, 1000원, ...)
- **입력**: 동전 투입 또는 버튼 누르기
- **출력**: 거스름돈 또는 음료수
- **전이**: 현재 상태 + 입력 → 다음 상태

핵심: 기계는 **"현재 상태"라는 단 하나의 정보**로 과거 전체를 요약한다. 1000원이 어떤 동전 조합으로 만들어졌는지는 기억하지 않고, "현재 1000원 상태"라는 것만 기억한다!

### 1.2 형식적 정의

> **정의 1** (Rosen 정의 1)
> **유한상태 기계**(finite-state machine) M = (S, I, O, f, g, s₀)는 다음으로 구성된다:
> - **S**: **상태**(state)의 유한집합
> - **I**: **입력 알파벳**(input alphabet)의 유한집합
> - **O**: **출력 알파벳**(output alphabet)의 유한집합
> - **f**: **전이함수**(transition function) — f : S × I → S
> - **g**: **출력함수**(output function) — g : S × I → O
> - **s₀**: **초기 상태**(initial state) — s₀ ∈ S

이 정의에서 출력이 **(상태, 입력) 쌍**에 의해 결정되는 기계를 **밀리 기계**(Mealy machine)라 한다.

> 📌 **무어 기계**(Moore machine)는 출력이 **상태만**에 의해 결정되는 변형이다. 즉 출력함수가 g : S → O인 형태이다.

### 1.3 상태표와 상태도

유한상태 기계를 표현하는 두 가지 방법:

#### **상태표**(State Table)

모든 (상태, 입력) 쌍에 대해 다음 상태와 출력을 표로 정리한다.

**예제** (Rosen 예제 1): S = {s₀, s₁, s₂, s₃}, I = {0, 1}, O = {0, 1}

|  | f(s, 0) | f(s, 1) | g(s, 0) | g(s, 1) |
|--|---------|---------|---------|---------|
| s₀ | s₁ | s₀ | 1 | 0 |
| s₁ | s₃ | s₀ | 1 | 1 |
| s₂ | s₁ | s₂ | 0 | 1 |
| s₃ | s₂ | s₁ | 0 | 0 |

#### **상태도**(State Diagram)

방향 그래프로 기계를 시각화한다:
- **원** = 상태
- **화살표** = 전이 (레이블: 입력, 출력)
- **Start →** 화살표 = 시작 상태를 가리킴

### 1.4 기계의 실행

입력 문자열 x = x₁x₂...xₖ가 주어지면:
1. 시작 상태 s₀에서 출발
2. x₁을 읽고: 다음 상태 s₁ = f(s₀, x₁), 출력 y₁ = g(s₀, x₁)
3. x₂를 읽고: 다음 상태 s₂ = f(s₁, x₂), 출력 y₂ = g(s₁, x₂)
4. ...반복...
5. 최종 출력: y₁y₂...yₖ

### 1.5 Lean 4에서의 모델링

```lean
-- 출력이 있는 유한상태 기계 (밀리 기계)
structure MealyMachine (S I O : Type) where
  transition : S → I → S      -- 전이함수 f
  output     : S → I → O      -- 출력함수 g
  initial    : S               -- 초기 상태 s₀

-- 기계 실행: 입력 리스트 → 출력 리스트
def MealyMachine.run (m : MealyMachine S I O)
    (inputs : List I) : List O :=
  let rec go (s : S) : List I → List O
    | []      => []
    | i :: is => m.output s i :: go (m.transition s i) is
  go m.initial inputs
```

---

## 2. 유한상태 기계의 응용

### 2.1 단위시간 지연장치 (Rosen 예제 5)

**목표**: 입력 x₁x₂...xₖ → 출력 0x₁x₂...xₖ₋₁ (한 칸씩 밀기)

| 입력 | 1 | 0 | 1 | 1 | 0 |
|------|---|---|---|---|---|
| 출력 | **0** | **1** | **0** | **1** | **1** |

**설계**: 상태가 "직전 입력"을 기억하면 된다.
- s₀: 시작 (이전 입력 없음) → 출력 0
- s₁: 이전 입력 = 1 → 출력 1
- s₂: 이전 입력 = 0 → 출력 0

```lean
inductive DState where | start | was1 | was0
  deriving DecidableEq, Repr

inductive Bit where | b0 | b1
  deriving DecidableEq, Repr

open DState Bit

def delayMachine : MealyMachine DState Bit Bit := {
  initial := start
  transition := fun _ i => match i with
    | b1 => was1 | b0 => was0
  output := fun s _ => match s with
    | start => b0 | was1 => b1 | was0 => b0
}

-- 테스트: 입력 [1,0,1,1,0] → 출력 [0,1,0,1,1]
#eval delayMachine.run [b1, b0, b1, b1, b0]
-- 결과: [b0, b1, b0, b1, b1] ✅
```

### 2.2 이진수 덧셈기 (Rosen 예제 6)

**목표**: 두 이진수를 오른쪽부터 한 자리씩 더한다. **올림수**(carry)를 기억해야 한다!

- s₀: 올림수 = 0
- s₁: 올림수 = 1

| 상태 | 입력 (x,y) | x+y+carry | 출력(합) | 다음 상태 |
|------|-----------|-----------|---------|----------|
| s₀ | (0,0) | 0 | 0 | s₀ |
| s₀ | (0,1) | 1 | 1 | s₀ |
| s₀ | (1,0) | 1 | 1 | s₀ |
| s₀ | (1,1) | 2=10₂ | 0 | s₁ |
| s₁ | (0,0) | 1 | 1 | s₀ |
| s₁ | (0,1) | 2=10₂ | 0 | s₁ |
| s₁ | (1,0) | 2=10₂ | 0 | s₁ |
| s₁ | (1,1) | 3=11₂ | 1 | s₁ |

```lean
inductive Carry where | c0 | c1
  deriving DecidableEq, Repr

open Carry Bit

def adder : MealyMachine Carry (Bit × Bit) Bit := {
  initial := c0
  transition := fun s (x, y) => match s, x, y with
    | c0, b0, b0 => c0 | c0, b0, b1 => c0
    | c0, b1, b0 => c0 | c0, b1, b1 => c1
    | c1, b0, b0 => c0 | c1, b0, b1 => c1
    | c1, b1, b0 => c1 | c1, b1, b1 => c1
  output := fun s (x, y) => match s, x, y with
    | c0, b0, b0 => b0 | c0, b0, b1 => b1
    | c0, b1, b0 => b1 | c0, b1, b1 => b0
    | c1, b0, b0 => b1 | c1, b0, b1 => b0
    | c1, b1, b0 => b0 | c1, b1, b1 => b1
}

-- 테스트: 5 + 3 = 101₂ + 011₂
-- 오른쪽부터: (1,1), (0,1), (1,0), (0,0)
#eval adder.run [(b1,b1), (b0,b1), (b1,b0), (b0,b0)]
-- 결과: [b0, b0, b0, b1] → 역순으로 읽으면 1000₂ = 8 ✅
```

### 2.3 패턴 인식: "111" 감지 (Rosen 예제 7)

**목표**: 1이 **연속 3번** 나오면 출력 1

**설계**:
- s₀: 연속 1이 0개
- s₁: 연속 1이 1개
- s₂: 연속 1이 2개 이상

```lean
inductive PState where | p0 | p1 | p2
  deriving DecidableEq, Repr

open PState Bit

def detect111 : MealyMachine PState Bit Bit := {
  initial := p0
  transition := fun s i => match s, i with
    | _, b0 => p0    -- 0이 오면 리셋
    | p0, b1 => p1   -- 연속1: 0→1개
    | p1, b1 => p2   -- 연속1: 1→2개
    | p2, b1 => p2   -- 연속1: 2개 이상 유지
  output := fun s i => match s, i with
    | p2, b1 => b1   -- 연속 3번째 1 → 출력 1!
    | _,  _  => b0
}

-- 테스트: 10111010
#eval detect111.run [b1,b0,b1,b1,b1,b0,b1,b0]
-- 결과: [b0,b0,b0,b0,b1,b0,b0,b0] ✅ (5번째에서 111 감지)
```

---

## 3. 결정적 유한상태 오토마톤 (DFA)

### 3.1 출력을 없애고 "수용/거부"로 바꾸기

언어 인식이 목적이면, 매 입력마다 출력을 낼 필요가 없다. 대신:
1. 입력을 **전부** 읽는다
2. 마지막에 도달한 상태가 **최종 상태**(수용 상태)인지 확인한다
3. 최종 상태이면 **"수용"**(accept), 아니면 **"거부"**(reject)

### 3.2 DFA의 형식적 정의

> **정의 3** (Rosen 정의 3)
> **결정적 유한상태 오토마톤**(DFA) M = (S, I, f, s₀, F):
> - **S**: 상태의 유한집합
> - **I**: 입력 알파벳
> - **f**: 전이함수 f : S × I → S
> - **s₀**: 시작 상태
> - **F** ⊆ S: **최종 상태**(final states, 수용 상태) 집합

밀리 기계와의 차이:
- 출력 알파벳 O **없음**
- 출력함수 g **없음**
- 대신 **최종 상태 집합 F** 있음

> 💡 상태도에서 최종 상태는 **이중 원**(◎)으로 표시한다!

### 3.3 DFA가 문자열을 수용하는 조건

> **정의 4** (Rosen 정의 4)
> 문자열 x = x₁x₂...xₖ가 DFA M에 의해 **인식**(수용)되려면:
> s₀에서 출발하여 x를 모두 읽은 후 도달하는 상태 f*(s₀, x)가 **F에 속해야** 한다.
>
> M이 **인식하는 언어**: L(M) = {x ∈ I* | f*(s₀, x) ∈ F}

### 3.4 Lean 4에서의 DFA

```lean
-- 결정적 유한상태 오토마톤
structure DFA (S I : Type) where
  transition : S → I → S
  initial    : S
  accepting  : S → Bool      -- F의 멤버십 함수

-- 입력을 전부 읽은 후의 상태
def DFA.finalState (m : DFA S I) (inputs : List I) : S :=
  inputs.foldl m.transition m.initial

-- 수용 여부 판별
def DFA.accepts (m : DFA S I) (inputs : List I) : Bool :=
  m.accepting (m.finalState inputs)
```

### 3.5 DFA 예제: 짝수 개의 0을 가진 비트열

**설계**:
- s₀ (시작, **수용**): 0의 개수 = 짝수 (0개도 짝수!)
- s₁: 0의 개수 = 홀수

| 상태 | 입력 0 | 입력 1 |
|------|--------|--------|
| s₀ (**수용**) | s₁ | s₀ |
| s₁ | s₀ | s₁ |

규칙: 0이 들어올 때만 상태가 바뀌고, 1이 들어오면 상태 유지.

```
       1               1
      ┌──┐            ┌──┐
      │  ▼            │  ▼
    ┌─────┐    0    ┌─────┐
──►│◎ s₀ │ ──────► │  s₁ │
    └─────┘ ◄────── └─────┘
               0
```

```lean
inductive EvenOdd where | even | odd
  deriving DecidableEq, Repr

open EvenOdd Bit

def evenZeros : DFA EvenOdd Bit := {
  initial := even
  transition := fun s i => match s, i with
    | even, b0 => odd   | even, b1 => even
    | odd,  b0 => even  | odd,  b1 => odd
  accepting := fun s => match s with
    | even => true | odd => false
}

-- 테스트
#eval evenZeros.accepts []              -- true (0개 = 짝수)
#eval evenZeros.accepts [b1, b1, b1]    -- true (0이 0개)
#eval evenZeros.accepts [b0]            -- false (0이 1개)
#eval evenZeros.accepts [b0, b1, b0]    -- true (0이 2개)
#eval evenZeros.accepts [b0, b0, b0]    -- false (0이 3개)
```

### 3.6 DFA 예제: "01"로 끝나는 비트열

**설계**: 마지막 두 글자가 "01"인지 추적
- s₀ (시작): 아직 패턴 매칭 안 됨
- s₁: 직전 입력 = 0
- s₂ (**수용**): 직전 두 입력 = 01

```lean
inductive EndState where | start | saw0 | saw01
  deriving DecidableEq, Repr

open EndState Bit

def endsWith01 : DFA EndState Bit := {
  initial := start
  transition := fun s i => match s, i with
    | _,     b0 => saw0     -- 0을 보면 항상 saw0
    | start, b1 => start    -- 1을 보면 리셋
    | saw0,  b1 => saw01    -- 0 다음에 1 → 01 완성!
    | saw01, b1 => start    -- 01 이후 1 → 리셋
  accepting := fun s => match s with
    | saw01 => true | _ => false
}

-- 테스트
#eval endsWith01.accepts [b0, b1]           -- true  "01"
#eval endsWith01.accepts [b1, b0, b1]       -- true  "101"
#eval endsWith01.accepts [b0, b1, b0]       -- false "010"
#eval endsWith01.accepts [b1, b1, b0, b1]   -- true  "1101"
```

---

## 4. DFA 설계 전략

DFA를 설계할 때의 핵심 사고방식:

### 4.1 "상태 = 지금까지의 요약"

**각 상태는 "지금까지 읽은 입력의 핵심 정보"를 요약한다.**

예시:
- "짝수 개의 0" → 상태 = {짝수, 홀수} (0의 개수의 홀짝만 기억)
- "01로 끝남" → 상태 = {시작, 0봄, 01봄} (마지막 1~2글자만 기억)
- "111 포함" → 상태 = {연속1: 0개, 1개, 2개, 3개이상} (연속 1의 개수만 기억)

### 4.2 설계 절차

1. **"무엇을 기억해야 하는가?"** 생각하기
2. 그 정보를 표현할 수 있는 **상태** 정의하기
3. 각 상태에서 각 입력에 대한 **전이** 결정하기
4. **어떤 상태가 수용 상태인지** 결정하기
5. 몇 가지 문자열로 **검증**하기

---

## 5. 연습문제

### 연습 5.1: 상태표에서 출력 구하기 [괄호 채우기]

예제 1의 상태표를 사용하여 입력 101011에 대한 출력을 구하라.

```
입력:  1     0     1     0     1     1
상태:  s₀ →  ⬜  →  ⬜  →  ⬜  →  ⬜  →  ⬜  →  ⬜
출력:  ⬜     ⬜     ⬜     ⬜     ⬜     ⬜
```

<details>
<summary>📝 답 보기</summary>

```
입력:  1     0     1     0     1     1
상태:  s₀ → s₀ → s₁ → s₀ → s₁ → s₀ → s₀
출력:  0     1     0     1     0     0

설명:
- s₀에서 1 → 다음 s₀, 출력 0
- s₀에서 0 → 다음 s₁, 출력 1
- s₁에서 1 → 다음 s₀, 출력 1 (표에서 확인!)
  수정: s₁에서 1 → 다음 s₀, 출력 1
- s₀에서 0 → 다음 s₁, 출력 1
- s₁에서 1 → 다음 s₀, 출력 1
  수정: s₀에서 1 → 다음 s₀, 출력 0
최종 출력: 011100
```

정확한 추적:

| 단계 | 현재 상태 | 입력 | f(s,i) | g(s,i) |
|------|----------|------|--------|--------|
| 1 | s₀ | 1 | s₀ | 0 |
| 2 | s₀ | 0 | s₁ | 1 |
| 3 | s₁ | 1 | s₀ | 1 |
| 4 | s₀ | 0 | s₁ | 1 |
| 5 | s₁ | 1 | s₀ | 1 |
| 6 | s₀ | 1 | s₀ | 0 |

출력: **011110**

</details>

---

### 연습 5.2: 단위시간 지연장치 구현 [skeleton]

다음 Lean 4 코드의 빈칸을 채워 단위시간 지연장치를 완성하라.

```lean
inductive DS where | start | was1 | was0
open DS Bit

def delay : MealyMachine DS Bit Bit := {
  initial := ⬜
  transition := fun _ i => match i with
    | b1 => ⬜ | b0 => ⬜
  output := fun s _ => match s with
    | start => ⬜ | was1 => ⬜ | was0 => ⬜
}
```

<details>
<summary>📝 답 보기</summary>

```lean
def delay : MealyMachine DS Bit Bit := {
  initial := start
  transition := fun _ i => match i with
    | b1 => was1 | b0 => was0
  output := fun s _ => match s with
    | start => b0 | was1 => b1 | was0 => b0
}
```

핵심: 전이함수는 입력만으로 결정(이전 입력을 기억), 출력함수는 상태만으로 결정(기억된 이전 입력을 출력).

</details>

---

### 연습 5.3: DFA 수용 여부 판별 [괄호 채우기]

"짝수 개의 0" DFA에서 다음 문자열의 수용 여부를 판별하라.

```
(a) 1101    : 0의 개수 = ⬜ → 짝수/홀수 → 수용/거부: ⬜
(b) 00100   : 0의 개수 = ⬜ → 짝수/홀수 → 수용/거부: ⬜
(c) λ(빈 문자열): 0의 개수 = ⬜ → 짝수/홀수 → 수용/거부: ⬜
(d) 000000  : 0의 개수 = ⬜ → 짝수/홀수 → 수용/거부: ⬜
```

<details>
<summary>📝 답 보기</summary>

```
(a) 1101    : 0의 개수 = 1 → 홀수 → 거부
(b) 00100   : 0의 개수 = 4 → 짝수 → 수용
(c) λ       : 0의 개수 = 0 → 짝수 → 수용
(d) 000000  : 0의 개수 = 6 → 짝수 → 수용
```

</details>

---

### 연습 5.4: DFA 설계 — "1로 끝나는 비트열" [sorry]

1로 끝나는 비트열을 수용하는 DFA를 설계하라.

```lean
-- 상태: 2개면 충분하다. 어떤 정보를 기억해야 할까?
-- 힌트: "마지막 입력이 1인지 0인지"만 기억하면 된다!

inductive LS where | last0or_start | last1
  deriving DecidableEq, Repr

open LS Bit

def endsWith1 : DFA LS Bit := {
  initial := sorry
  transition := sorry
  accepting := sorry
}

-- 테스트
#eval endsWith1.accepts [b1]           -- true
#eval endsWith1.accepts [b0]           -- false
#eval endsWith1.accepts [b1, b0, b1]   -- true
#eval endsWith1.accepts [b1, b0]       -- false
#eval endsWith1.accepts []             -- false
```

<details>
<summary>📝 답 보기</summary>

```lean
def endsWith1 : DFA LS Bit := {
  initial := last0or_start
  transition := fun _ i => match i with
    | b1 => last1
    | b0 => last0or_start
  accepting := fun s => match s with
    | last1 => true
    | last0or_start => false
}
```

</details>

---

### 연습 5.5: DFA 설계 — "00을 포함하는 비트열" [sorry]

연속으로 0이 2번 이상 나오는 비트열을 수용하는 DFA를 설계하라.

```lean
-- 힌트: 상태 3개가 필요하다
-- s₀: 아직 연속 0을 본 적 없음 (또는 직전이 1)
-- s₁: 직전 입력이 0 (연속 0이 1개)
-- s₂: 연속 00을 이미 보았음 (수용 상태, 이후 입력 무관)

inductive ContState where | noZero | oneZero | found00
  deriving DecidableEq, Repr

def contains00 : DFA ContState Bit := {
  initial := sorry
  transition := sorry
  accepting := sorry
}
```

<details>
<summary>📝 답 보기</summary>

```lean
open ContState Bit

def contains00 : DFA ContState Bit := {
  initial := noZero
  transition := fun s i => match s, i with
    | found00, _ => found00    -- 이미 00을 찾았으면 상태 유지
    | _, b1 => noZero          -- 1이 오면 연속0 리셋
    | noZero, b0 => oneZero    -- 처음 0
    | oneZero, b0 => found00   -- 연속 두 번째 0 → 00 발견!
  accepting := fun s => match s with
    | found00 => true | _ => false
}
```

핵심: `found00` 상태에 한번 도달하면 어떤 입력이 와도 계속 `found00`에 머무른다. "00을 포함한다"는 사실은 이후 입력으로 바뀌지 않기 때문이다!

</details>

---

### 연습 5.6: 종합 — 이진수 덧셈기 추적 [괄호 채우기]

이진수 덧셈기로 3 + 5 = 011₂ + 101₂를 계산하라.

오른쪽 자릿수부터 입력: (1,1), (1,0), (0,1), (0,0)

```
단계 1: 상태 c0, 입력 (1,1), 1+1+0 = 2 = 10₂
        출력 = ⬜, 다음 상태 = ⬜

단계 2: 상태 ⬜, 입력 (1,0), 1+0+⬜ = ⬜
        출력 = ⬜, 다음 상태 = ⬜

단계 3: 상태 ⬜, 입력 (0,1), 0+1+⬜ = ⬜
        출력 = ⬜, 다음 상태 = ⬜

단계 4: 상태 ⬜, 입력 (0,0), 0+0+⬜ = ⬜
        출력 = ⬜, 다음 상태 = ⬜

결과 (역순): ⬜ = ⬜ (십진수)
```

<details>
<summary>📝 답 보기</summary>

```
단계 1: 상태 c0, 입력 (1,1), 1+1+0 = 2 = 10₂
        출력 = 0, 다음 상태 = c1

단계 2: 상태 c1, 입력 (1,0), 1+0+1 = 2 = 10₂
        출력 = 0, 다음 상태 = c1

단계 3: 상태 c1, 입력 (0,1), 0+1+1 = 2 = 10₂
        출력 = 0, 다음 상태 = c1

단계 4: 상태 c1, 입력 (0,0), 0+0+1 = 1
        출력 = 1, 다음 상태 = c0

결과 (역순): 1000₂ = 8 (십진수) ✅ (3 + 5 = 8)
```

</details>

---

## 6. 핵심 요약

| 개념 | 정의 | Lean 4 |
|------|------|--------|
| **유한상태 기계**(FSM) | (S, I, O, f, g, s₀) | `MealyMachine S I O` |
| **전이함수** f | S × I → S | `transition : S → I → S` |
| **출력함수** g | S × I → O | `output : S → I → O` |
| **상태표** | (상태, 입력) → (다음 상태, 출력) | `match s, i with ...` |
| **상태도** | 방향 그래프 | (시각적 표현) |
| **밀리 기계**(Mealy) | 출력 = f(상태, 입력) | 이 파트의 기본 정의 |
| **무어 기계**(Moore) | 출력 = f(상태) | 변형 |
| **DFA** | (S, I, f, s₀, F) | `DFA S I` |
| **최종 상태** F | 수용 상태의 집합 | `accepting : S → Bool` |
| **인식**(수용) | 읽은 후 F에 도달 | `DFA.accepts` |
| **설계 핵심** | 상태 = 과거의 요약 | "무엇을 기억할까?" |

---

## 다음 파트 예고

**Part 15-C**에서는:
- **비결정적 유한상태 오토마톤**(NFA) — 여러 가능한 다음 상태
- NFA와 DFA의 **동치 관계** — 부분집합 구성법
- **정규 표현식**(regular expression)과 정규 언어
- **클레이니 정리** — 정규 표현식 ↔ 유한상태 오토마톤 ↔ 정규 문법
- **펌핑 보조정리**(pumping lemma) — DFA로 인식할 수 없는 언어
- **튜링 기계** 소개
