# Lean4 완전 정복 가이드 —  Part 12-C: n항 관계와 응용 (n-ary Relations and Applications)

> **Rosen 이산수학 8판 · Section 9.2 기반**
> 『Mathematics in Lean』 + Lean 4 공식화

---

## 0. 들어가며: 이 파트에서 배울 것

Part 12-A에서는 **이진관계**(binary relation)의 기본 성질(반사적, 대칭적, 추이적 등)을 다루었다. 이번 Part 12-C에서는 **셋 이상의 집합** 사이의 관계, 즉 **n항 관계**(n-ary relation)를 다룬다. n항 관계는 **관계 데이터베이스**(relational database)의 수학적 기초이다!

이 파트에서는 다음을 다룬다:

1. **n항 관계**(n-ary relation)의 정의와 직관
2. **관계 데이터베이스**(relational database)의 개념: 레코드, 필드, 테이블
3. **기본 키**(primary key)와 **합성 키**(composite key)
4. **선택 연산자**(selection operator)와 **투사**(projection)
5. **결합 연산**(join operation)
6. **SQL**과의 관계
7. **데이터마이닝**: 연관 법칙(association rules)

### 이 파트에서 사용하는 핵심 Lean 4 개념

| 개념 | 설명 |
|------|------|
| `(α × β × γ)` | 튜플(n개 한 벌)로 n항 관계 표현 |
| `structure` | 레코드(구조체) 정의 |
| `List.filter` | 선택 연산자(조건 필터링) |
| `List.map` | 투사(필드 추출) |
| `Decidable` | 조건 판정 가능성 |
| `deriving Repr, DecidableEq` | 자동 인스턴스 생성 |

---

## 1. n항 관계란 무엇인가?

### 1.1 이진관계에서 n항 관계로

Part 12-A에서 배운 **이진관계**(binary relation)는 **두 집합** 사이의 관계였다. 예를 들어, "학생 x는 과목 y를 수강한다"는 학생 집합과 과목 집합 사이의 이진관계이다.

그런데 현실에서는 **셋 이상의 집합**이 관련되는 경우가 많다. 예를 들어:

- 학생의 이름, 학번, 전공, 학점 → **4개**의 정보가 하나로 묶인다
- 항공편의 항공사, 편명, 출발지, 목적지, 출발시간 → **5개**의 정보가 하나로 묶인다

이렇게 **여러 집합의 원소들을 한꺼번에 묶는 관계**가 n항 관계이다.

**비유**: 이진관계가 "두 사람 사이의 악수"라면, n항 관계는 "여러 사람이 함께 손을 맞잡는 것"이다. 데이터베이스의 테이블 한 줄(행)이 바로 이 "n개의 손을 맞잡은 상태"이다.

### 1.2 형식적 정의

> **정의 1** (Rosen): A₁, A₂, ..., Aₙ이 집합이라고 하자. 이 집합들에 대한 **n항 관계**(n-ary relation)는 A₁ × A₂ × ⋯ × Aₙ의 부분집합이다. A₁, A₂, ..., Aₙ을 관계의 **정의역**(domain)이라고 하고, n을 **차수**(degree)라고 한다.

쉽게 말해서:

- **2항 관계**: 순서쌍 (a, b)의 집합 → 차수 2
- **3항 관계**: 순서 3-벌 (a, b, c)의 집합 → 차수 3
- **n항 관계**: 순서 n-벌 (a₁, a₂, ..., aₙ)의 집합 → 차수 n

### 1.3 예제로 이해하기

**예제 1** (Rosen): R이 a, b, c가 정수이고 a < b < c인 3항 (a, b, c)로 구성되는 ℕ × ℕ × ℕ에 대한 관계라고 하자.

- (1, 2, 3) ∈ R이다 (1 < 2 < 3이므로)
- (2, 4, 3) ∉ R이다 (4 < 3이 아니므로)
- 이 관계의 차수는 3이다
- 정의역들은 모두 자연수의 집합과 같다

```lean
-- 예제 1: a < b < c인 3항 관계
def R_ex1 : Set (ℕ × ℕ × ℕ) :=
  { t | t.1 < t.2.1 ∧ t.2.1 < t.2.2 }

-- (1, 2, 3) ∈ R_ex1 임을 증명
example : (1, 2, 3) ∈ R_ex1 := by
  -- R_ex1의 정의를 펼치면 1 < 2 ∧ 2 < 3
  constructor
  · norm_num   -- 1 < 2
  · norm_num   -- 2 < 3

-- (2, 4, 3) ∉ R_ex1 임을 증명
example : (2, 4, 3) ∉ R_ex1 := by
  -- 4 < 3이 거짓이므로 전체가 거짓
  intro ⟨_, h⟩
  omega  -- 4 < 3은 모순
```

여기서 Lean 4의 **튜플**(tuple) 표기법을 주목하자:

- `(1, 2, 3)`은 사실 `(1, (2, 3))`이다. Lean 4에서 3-튜플은 **중첩된 쌍**(nested pair)이다.
- `t.1`은 첫 번째 원소, `t.2.1`은 두 번째 원소, `t.2.2`는 세 번째 원소이다.
- 이것은 수학에서의 (a, b, c)와 완전히 대응된다.

**예제 2** (Rosen): R이 a, b, c가 정수이고 등차수열인 3항 (a, b, c)에 대한 관계라고 하자. 즉, (a, b, c) ∈ R은 b − a = c − b, 다시 말해 b = a + k이고 c = a + 2k인 정수 k가 존재한다는 것과 동치이다.

```lean
-- 예제 2: 등차수열 관계 (정수 사용)
def R_arith : Set (ℤ × ℤ × ℤ) :=
  { t | t.2.1 - t.1 = t.2.2 - t.2.1 }

-- (1, 3, 5) ∈ R_arith: 3 - 1 = 5 - 3 = 2
example : (1, 3, 5) ∈ R_arith := by
  show 3 - 1 = 5 - 3
  norm_num

-- (2, 5, 9) ∉ R_arith: 5 - 2 = 3이지만 9 - 5 = 4
example : (2, 5, 9) ∉ R_arith := by
  intro h
  show 5 - 2 = 9 - 5 at h  -- 이것은 형식적으로는 더 복잡할 수 있음
  omega
```

### 1.4 Lean 4에서 구조체(structure)로 n항 관계 표현하기

튜플 대신 **구조체**(structure)를 사용하면 각 필드에 이름을 붙일 수 있어서 더 읽기 쉽다. 이것이 바로 데이터베이스에서의 **레코드**(record) 개념과 정확히 대응된다!

```lean
-- 학생 레코드 정의 (Rosen 표 1과 동일)
structure StudentRecord where
  name   : String      -- 학생 이름
  idNum  : ℕ           -- 학번
  major  : String      -- 전공
  gpa    : Float       -- 학점
  deriving Repr, DecidableEq

-- 예시 데이터 (Rosen 표 1)
def ackermann : StudentRecord := ⟨"Ackermann", 231455, "Computer Science", 3.88⟩
def adams     : StudentRecord := ⟨"Adams",     888323, "Physics",          3.45⟩
def chou      : StudentRecord := ⟨"Chou",      102147, "Computer Science", 3.49⟩
def goodfriend: StudentRecord := ⟨"Goodfriend",453876, "Mathematics",      3.45⟩
def rao       : StudentRecord := ⟨"Rao",       678543, "Mathematics",      3.90⟩
def stevens   : StudentRecord := ⟨"Stevens",   786576, "Psychology",       2.99⟩

-- 데이터베이스 (레코드의 리스트)
def studentDB : List StudentRecord :=
  [ackermann, adams, chou, goodfriend, rao, stevens]
```

> **핵심 포인트**: Lean 4의 `structure`는 수학의 n항 관계에서 한 벌(n-tuple)의 구조를 **이름 붙인 필드**로 정의한 것이다. `deriving Repr`는 출력을 가능하게 하고, `deriving DecidableEq`는 같은지 비교할 수 있게 해준다.

---

## 2. 관계 데이터베이스 (Relational Database)

### 2.1 개념 설명

**관계 데이터베이스**(relational database)는 **관계의 개념에 기반한 데이터 모델**(relational data model)로 데이터를 저장하고 관리하는 시스템이다. 에드거 코드(Edgar F. Codd)가 1970년에 제안했으며, 오늘날 거의 모든 데이터베이스의 기초이다.

핵심 용어를 정리하자:

| 수학 용어 | 데이터베이스 용어 | 설명 |
|----------|--------------|------|
| n항 관계 | **테이블**(table) | 데이터의 표 |
| n개 한 벌(n-tuple) | **레코드**(record) / 행(row) | 테이블의 한 줄 |
| 정의역(domain) | **속성**(attribute) / 열(column) | 데이터의 종류 |
| 부분집합의 원소 | **필드**(field) | 한 칸의 값 |

**비유**: 데이터베이스 테이블은 엑셀 스프레드시트와 비슷하다. 각 열(column)이 속성이고, 각 행(row)이 레코드이다.

### 2.2 기본 키와 합성 키

> **정의**: n항 관계의 **정의역**(domain)은, n개 한 벌에서 이 정의역의 값이 n개 한 벌을 결정할 때 **기본 키**(primary key)라고 부른다. 즉, 관계에서 정의역의 값이 같은 두 n개 한 벌이 없을 때 이 정의역이 기본 키가 된다.

쉽게 말해서, **기본 키**는 "이 값만 알면 누구인지 정확히 알 수 있는 필드"이다.

**예**: 학생 데이터베이스에서:
- **학생 이름**: 기본 키가 될 수 있다 (같은 이름이 없다면, 하지만 현실에서는 동명이인이 있으므로 위험!)
- **학번**: 기본 키가 될 수 있다 (학번은 유일하므로)
- **전공**: 기본 키가 될 수 **없다** (같은 전공의 학생이 여럿)
- **학점**: 기본 키가 될 수 **없다** (같은 학점의 학생이 여럿)

```lean
-- 기본 키 판정: 이름이 기본 키인지?
-- 같은 이름의 학생이 없으면 기본 키이다
def isPrimaryKey_name (db : List StudentRecord) : Prop :=
  ∀ r1 r2 : StudentRecord, r1 ∈ db → r2 ∈ db → r1.name = r2.name → r1 = r2

-- 학번이 기본 키인지?
def isPrimaryKey_id (db : List StudentRecord) : Prop :=
  ∀ r1 r2 : StudentRecord, r1 ∈ db → r2 ∈ db → r1.idNum = r2.idNum → r1 = r2

-- 전공이 기본 키인지?
-- 반례: Ackermann과 Chou 모두 "Computer Science" → 기본 키 아님
-- Goodfriend와 Rao 모두 "Mathematics" → 기본 키 아님
```

> **정의**: **합성 키**(composite key)는 정의역의 집합의 값으로 n개 한 벌을 결정할 때, 이 정의역들의 데카르트 곱(Cartesian product)을 말한다.

합성 키는 하나의 필드로는 유일하게 식별할 수 없지만, **여러 필드를 조합**하면 유일하게 식별할 수 있는 경우이다.

```lean
-- 합성 키 예시: (전공, 학점)이 합성 키인가?
-- Rosen 예제 6: 전공과 학점이 같은 4개 한 벌이 없으므로 합성 키이다
-- 주의: Goodfriend와 Adams 모두 GPA = 3.45지만 전공이 다르다
-- 따라서 (Major, GPA) 조합으로 유일하게 식별 가능
```

---

## 3. 선택 연산자 (Selection Operator)

### 3.1 개념 설명

n항 관계에 관한 가장 기본적인 연산은 **어떤 조건을 만족하는 n개 한 벌**을 찾는 것이다. 이것이 **선택 연산자**(selection operator)이다.

> **정의 2** (Rosen): R이 n항 관계이고 C를 R이 만족할 수 있는 조건이라 하자. 그러면 **선택 연산자**(selection operator) s_C는 n항 관계 R에서 조건 C를 만족하는 모든 n개 한 벌의 n항 관계를 선택한다.

**비유**: 선택 연산자는 "필터"이다. 체로 쌀을 걸러내듯, 조건에 맞는 레코드만 걸러낸다.

### 3.2 Lean 4에서의 구현

```lean
-- 선택 연산자: 조건을 만족하는 레코드만 필터링
def select (db : List StudentRecord) (cond : StudentRecord → Bool) : List StudentRecord :=
  db.filter cond

-- 예제 7 (Rosen): 컴퓨터과학 전공 학생 찾기
-- 조건: major = "Computer Science"
#eval select studentDB (fun r => r.major == "Computer Science")
-- 결과: [Ackermann (CS, 3.88), Chou (CS, 3.49)]

-- 평점 3.5 이상인 학생 찾기
#eval select studentDB (fun r => r.gpa > 3.5)
-- 결과: [Ackermann (CS, 3.88), Rao (Math, 3.90)]

-- 복합 조건: 컴퓨터과학 전공이면서 평점 3.5 이상
#eval select studentDB (fun r => r.major == "Computer Science" && r.gpa > 3.5)
-- 결과: [Ackermann (CS, 3.88)]
```

### 3.3 수학적 정의와 Lean 4 대응

수학에서 선택 연산자는 이렇게 정의된다:

`s_C(R) = { t ∈ R | C(t) }`

Lean 4에서의 대응:

```lean
-- 집합론적 정의 (명제 수준)
def selectSet (R : Set (ℕ × String × Float)) (C : ℕ × String × Float → Prop) :
    Set (ℕ × String × Float) :=
  { t ∈ R | C t }

-- 계산 가능한 정의 (프로그래밍 수준)
def selectList (R : List α) (C : α → Bool) : List α :=
  R.filter C
```

> **중요**: Lean 4에서는 **두 가지 세계**가 있다:
> 1. **명제 세계**(Prop): `Set`, `∈`, 증명 — 수학적 진리를 다룬다
> 2. **계산 세계**(Bool, List): `filter`, `map`, `#eval` — 실제 계산을 수행한다
> 
> 선택 연산자를 두 세계 모두에서 표현할 수 있다는 것이 Lean 4의 강점이다!

---

## 4. 투사 (Projection)

### 4.1 개념 설명

**투사**(projection)는 관계의 모든 레코드에서 **같은 필드를 삭제**하여 새로운 n항 관계를 만드는 연산이다.

> **정의 3** (Rosen): **투사**(projection) P_{i₁, i₂, ..., iₘ}는 n개 한 벌 (a₁, a₂, ..., aₙ)을 m개 한 벌 (a_{i₁}, a_{i₂}, ..., a_{iₘ})에 대응한다. 여기서, i₁ < i₂ < ⋯ < iₘ이고 m ≤ n이다.

쉽게 말해서, 투사는 "관심 있는 열(column)만 남기고 나머지를 버리는 것"이다.

**비유**: 학생 데이터베이스에서 이름과 학점만 궁금하다면, 학번과 전공 열을 삭제하는 것이 투사이다.

### 4.2 예제

**예제 8** (Rosen): 4개 한 벌 (2, 3, 0, 4)와 (Jane Doe, 234111001, Geography, 3.14)에 투사 P₁,₃을 적용한 결과는?

- (2, 3, 0, 4) → (2, 0) — 1번째와 3번째 성분만 남김
- (Jane Doe, 234111001, Geography, 3.14) → (Jane Doe, Geography) — 이름과 전공만 남김

### 4.3 Lean 4에서의 구현

```lean
-- 투사: 이름과 학점만 추출 (P_{1,4} in Rosen)
def projectNameGPA (db : List StudentRecord) : List (String × Float) :=
  db.map (fun r => (r.name, r.gpa))

#eval projectNameGPA studentDB
-- [("Ackermann", 3.88), ("Adams", 3.45), ("Chou", 3.49),
--  ("Goodfriend", 3.45), ("Rao", 3.90), ("Stevens", 2.99)]

-- 투사: 전공만 추출 (중복 포함)
def projectMajor (db : List StudentRecord) : List String :=
  db.map (fun r => r.major)

#eval projectMajor studentDB
-- ["Computer Science", "Physics", "Computer Science",
--  "Mathematics", "Mathematics", "Psychology"]
```

### 4.4 투사의 핵심 성질

투사를 적용하면 **행의 수가 줄어들 수 있다**! 왜냐하면 일부 필드를 삭제하면 **중복되는 행**이 생길 수 있기 때문이다.

```lean
-- 중복 제거된 투사 (집합론적으로는 자동 중복 제거)
def projectMajorDistinct (db : List StudentRecord) : List String :=
  (db.map (fun r => r.major)).eraseDups

#eval projectMajorDistinct studentDB
-- ["Computer Science", "Physics", "Mathematics", "Psychology"]
-- 6개 행에서 4개 행으로 줄어들었다!
```

---

## 5. 결합 연산 (Join Operation)

### 5.1 개념 설명

**결합**(join) 연산은 **같은 필드를 공유하는 두 테이블을 하나로 합치는** 연산이다. 이것은 데이터베이스에서 가장 중요한 연산 중 하나이다!

> **정의 4** (Rosen): R이 m차 관계이고 S이 n차 관계라 하자. p ≤ m이고 p ≤ n인 **결합**(join) Jₚ(R, S)는 모든 m + n − p개 한 벌로 구성되는 m + n − p차 관계로, m개 한 벌의 마지막 p개 성분이 n개 한 벌의 처음 p개 성분과 일치한다.

**비유**: 두 퍼즐 조각이 맞물리는 부분(공유 필드)을 기준으로 합치는 것이다.

### 5.2 Lean 4에서의 간단한 결합

```lean
-- 교수 강의 배정 (Rosen 표 5와 유사)
structure Teaching where
  professor : String
  department : String
  courseNum : ℕ
  deriving Repr, DecidableEq

-- 강의실 배정 (Rosen 표 6과 유사)
structure RoomSchedule where
  department : String
  courseNum : ℕ
  room : String
  time : String
  deriving Repr, DecidableEq

-- 결합된 결과
structure JoinedSchedule where
  professor : String
  department : String
  courseNum : ℕ
  room : String
  time : String
  deriving Repr

-- 결합 연산: department와 courseNum이 일치하는 레코드를 합침
def joinSchedules (ts : List Teaching) (rs : List RoomSchedule) : List JoinedSchedule :=
  ts.flatMap fun t =>
    (rs.filter fun r => t.department == r.department && t.courseNum == r.courseNum).map fun r =>
      ⟨t.professor, t.department, t.courseNum, r.room, r.time⟩
```

---

## 6. SQL과의 관계

### 6.1 SQL이란?

**SQL**(Structured Query Language)은 관계 데이터베이스의 질의 언어이다. SQL은 우리가 배운 선택, 투사, 결합 연산을 **선언적으로**(declaratively) 표현한다.

| 수학 연산 | SQL 구문 | Lean 4 대응 |
|---------|---------|-----------|
| **선택**(selection) | `WHERE` | `List.filter` |
| **투사**(projection) | `SELECT` | `List.map` |
| **결합**(join) | `FROM ... , ...` 또는 `JOIN` | `List.flatMap` + `filter` |

**주의**: SQL의 `SELECT`는 "선택"이 아니라 **투사**(projection)에 해당한다! 이름이 헷갈리기 쉽다.

### 6.2 예제 12 (Rosen): SQL로 항공편 질의

Rosen의 표 8 (항공편 데이터)에 대해:

```sql
SELECT Departure_time
FROM Flights
WHERE Destination='Detroit'
```

이것을 Lean 4로 번역하면:

```lean
structure Flight where
  airline : String
  flightNum : ℕ
  gate : ℕ
  destination : String
  departureTime : String
  deriving Repr

def flights : List Flight := [
  ⟨"Nadir", 122, 34, "Detroit",   "08:10"⟩,
  ⟨"Acme",  221, 22, "Denver",    "08:17"⟩,
  ⟨"Acme",  122, 33, "Anchorage", "08:22"⟩,
  ⟨"Acme",  323, 34, "Honolulu",  "08:30"⟩,
  ⟨"Nadir", 199, 13, "Detroit",   "08:47"⟩,
  ⟨"Acme",  222, 22, "Denver",    "09:10"⟩,
  ⟨"Nadir", 322, 34, "Detroit",   "09:44"⟩
]

-- SQL: SELECT Departure_time FROM Flights WHERE Destination='Detroit'
-- Lean 4: 선택(filter) 후 투사(map)
#eval (flights.filter (fun f => f.destination == "Detroit")).map (fun f => f.departureTime)
-- ["08:10", "08:47", "09:44"]
```

---

## 7. 데이터마이닝과 연관 법칙

### 7.1 트랜잭션과 아이템 집합

**데이터마이닝**(data mining)은 대규모 데이터에서 유용한 패턴을 찾아내는 분야이다. 그 중 **연관 법칙**(association rule)은 "어떤 상품을 사면 다른 상품도 살 가능성이 높다"는 규칙을 발견하는 기법이다.

> **정의 5** (Rosen): 트랜잭션의 집합 T = {t₁, t₂, ..., tₖ} (k는 양의 정수)에서 아이템 집합 I의 **빈도**(count)는 σ(I)로 표현하는데, 이 아이템 집합을 포함하는 트랜잭션의 개수이다.

- **아이템 집합**(itemset): 상품들의 모임
- **빈도**(count): 그 아이템 집합을 포함하는 트랜잭션 수
- **지지도**(support): 빈도 / 전체 트랜잭션 수 = σ(I) / |T|

### 7.2 연관 법칙의 지지도와 신뢰도

> **정의 6** (Rosen): 만약 I와 J가 트랜잭션의 집합 T의 부분집합이라면,
> - **지지도**(support): support(I → J) = σ(I ∪ J) / |T|
> - **신뢰도**(confidence): confidence(I → J) = σ(I ∪ J) / σ(I)

```lean
-- 연관 법칙을 Lean 4로 모델링
-- 트랜잭션 = 아이템의 리스트
def transactions : List (List String) := [
  ["apples", "pears", "mangos"],           -- 1
  ["pears", "cider"],                      -- 2
  ["apples", "cider", "donuts", "mangos"], -- 3
  ["apples", "pears", "cider", "donuts"],  -- 4
  ["apples", "cider", "donuts"],           -- 5
  ["pears", "cider", "donuts"],            -- 6
  ["pears", "donuts"],                     -- 7
  ["apples", "pears", "cider"]             -- 8
]

-- 아이템 집합 I를 포함하는 트랜잭션 수 (빈도)
def count (items : List String) (trans : List (List String)) : ℕ :=
  trans.filter (fun t => items.all (fun i => t.contains i)) |>.length

-- 지지도 계산
def support (items : List String) (trans : List (List String)) : Float :=
  (count items trans).toFloat / trans.length.toFloat

-- 예: σ({사과}) = 5, support({사과}) = 5/8 = 0.625
#eval count ["apples"] transactions        -- 5
#eval support ["apples"] transactions      -- 0.625

-- 예: σ({사과, 사이다}) = 4, support({사과, 사이다}) = 4/8 = 0.5
#eval count ["apples", "cider"] transactions   -- 4
#eval support ["apples", "cider"] transactions -- 0.5
```

### 7.3 예제 15 (Rosen): 연관 법칙의 지지도와 신뢰도

{사이다, 도넛} → {사과}의 지지도와 신뢰도는?

```lean
-- σ({사이다, 도넛, 사과}) = σ({사이다, 도넛} ∪ {사과})
#eval count ["cider", "donuts", "apples"] transactions  -- 3

-- support({사이다, 도넛} → {사과}) = σ({사이다, 도넛, 사과}) / |T| = 3/8 = 0.375
#eval support ["cider", "donuts", "apples"] transactions  -- 0.375

-- confidence({사이다, 도넛} → {사과})
-- = σ({사이다, 도넛, 사과}) / σ({사이다, 도넛})
#eval count ["cider", "donuts"] transactions  -- 4
-- confidence = 3/4 = 0.75
```

---

## 8. 연습 문제 — 레벨 1: 설명 및 괄호 채우기

### 연습 8.1: n항 관계 소속 판정

```lean
-- 3항 관계: a + b = c인 자연수 순서 3-벌의 집합
def R_sum : Set (ℕ × ℕ × ℕ) :=
  { t | t.1 + t.2.1 = t.2.2 }

-- (2, 3, 5) ∈ R_sum 증명하기
-- 2 + 3 = 5이므로 참이다
example : (2, 3, 5) ∈ R_sum := by
  show 2 + 3 = 5        -- 정의를 펼침
  /- 여기를 채우세요 -/

-- (1, 1, 3) ∉ R_sum 증명하기
-- 1 + 1 = 2 ≠ 3이므로 거짓이다
example : (1, 1, 3) ∉ R_sum := by
  intro h
  show 1 + 1 = 3 at h   -- 정의를 펼침
  /- 여기를 채우세요 -/
```

<details>
<summary>💡 답 보기</summary>

```lean
example : (2, 3, 5) ∈ R_sum := by
  show 2 + 3 = 5
  norm_num

example : (1, 1, 3) ∉ R_sum := by
  intro h
  simp [R_sum, Set.mem_setOf_eq] at h
  -- 또는 간단히:
  -- omega
```
</details>

### 연습 8.2: 선택 연산자 조건 완성

```lean
-- Rosen 연습문제 11: 항공편 데이터에서 목적지가 Detroit인 레코드 찾기
-- 조건 C: Destination = Detroit
def detroitFlights : List Flight :=
  flights.filter (fun f => /- 여기를 채우세요 -/)
```

<details>
<summary>💡 답 보기</summary>

```lean
def detroitFlights : List Flight :=
  flights.filter (fun f => f.destination == "Detroit")
```
</details>

### 연습 8.3: 투사 함수 작성

```lean
-- Rosen 연습문제 17: 항공편 테이블에서 P_{1,4}를 적용하여
-- (항공사, 목적지) 쌍만 추출하라
def projectAirlineDest : List (String × String) :=
  flights.map (fun f => /- 여기를 채우세요 -/)
```

<details>
<summary>💡 답 보기</summary>

```lean
def projectAirlineDest : List (String × String) :=
  flights.map (fun f => (f.airline, f.destination))
```
</details>

---

## 9. 연습 문제 — 레벨 2: skeleton 채우기

### 연습 9.1: Rosen 연습문제 1 — 조건을 만족하는 3-벌 나열

관계 {(a, b, c) | a, b, c는 0 < a < b < c < 5를 만족하는 정수이다}에 포함되는 모든 3인 순서쌍을 나열하라.

```lean
-- 조건: 0 < a < b < c < 5인 자연수 3-벌
def R_ex_1 : List (ℕ × ℕ × ℕ) :=
  sorry  -- 힌트: 가능한 값은 1, 2, 3, 4

-- 검증: 모든 원소가 조건을 만족하는지
example : ∀ t ∈ R_ex_1, 0 < t.1 ∧ t.1 < t.2.1 ∧ t.2.1 < t.2.2 ∧ t.2.2 < 5 := by
  sorry
```

<details>
<summary>💡 답 보기</summary>

```lean
def R_ex_1 : List (ℕ × ℕ × ℕ) :=
  [(1, 2, 3), (1, 2, 4), (1, 3, 4), (2, 3, 4)]

example : ∀ t ∈ R_ex_1, 0 < t.1 ∧ t.1 < t.2.1 ∧ t.2.1 < t.2.2 ∧ t.2.2 < 5 := by
  simp [R_ex_1]
  omega
```

**설명**: 0 < a이므로 a ≥ 1, c < 5이므로 c ≤ 4, a < b < c이므로 최소 3개의 서로 다른 값이 필요하다. 가능한 조합: (1,2,3), (1,2,4), (1,3,4), (2,3,4).
</details>

### 연습 9.2: 복합 선택 + 투사

```lean
-- Rosen 연습문제 13: 항공편에서 항공사가 Nadir이거나
-- 목적지가 Denver인 레코드를 선택하라
def ex9_2 : List Flight :=
  flights.filter (fun f => sorry)

-- 선택된 결과에서 (항공사, 편명)만 투사하라
def ex9_2_proj : List (String × ℕ) :=
  ex9_2.map (fun f => sorry)
```

<details>
<summary>💡 답 보기</summary>

```lean
def ex9_2 : List Flight :=
  flights.filter (fun f => f.airline == "Nadir" || f.destination == "Denver")

def ex9_2_proj : List (String × ℕ) :=
  ex9_2.map (fun f => (f.airline, f.flightNum))
```
</details>

### 연습 9.3: 빈도와 지지도 계산

```lean
-- Rosen 연습문제 33a와 유사: 다음 트랜잭션에서 "배"의 빈도와 지지도를 구하라
-- σ({pears}) = ?
-- support({pears}) = ?

#eval count ["pears"] transactions      -- 정답: ?
#eval support ["pears"] transactions    -- 정답: ?

-- σ({도넛, 배}) = ?
#eval count ["donuts", "pears"] transactions  -- 정답: ?
```

<details>
<summary>💡 답 보기</summary>

```lean
#eval count ["pears"] transactions        -- 5 (트랜잭션 1,2,4,6,7,8)
#eval support ["pears"] transactions      -- 0.625 = 5/8

#eval count ["donuts", "pears"] transactions  -- 3 (트랜잭션 4,6,7)
```
</details>

---

## 10. 연습 문제 — 레벨 3: sorry 채우기 (독립 증명)

### 연습 10.1: 선택 연산자의 교환 법칙 (Rosen 연습문제 20)

C₁과 C₂가 n항 관계 R의 원소들에 대한 조건일 때, s_{C₁}(s_{C₂}(R)) = s_{C₁∧C₂}(R)임을 증명하라.

```lean
-- 선택 연산자의 결합 성질
-- 필터를 두 번 적용하는 것 = 조건을 합쳐서 한 번 적용하는 것
theorem select_compose {α : Type} (R : List α) (C₁ C₂ : α → Bool) :
    (R.filter C₂).filter C₁ = R.filter (fun x => C₁ x && C₂ x) := by
  sorry
```

<details>
<summary>💡 힌트</summary>

`List.filter_filter`를 사용하면 된다. 또는 귀납법으로 리스트의 각 원소에 대해 증명할 수 있다.
</details>

<details>
<summary>💡 답 보기</summary>

```lean
theorem select_compose {α : Type} (R : List α) (C₁ C₂ : α → Bool) :
    (R.filter C₂).filter C₁ = R.filter (fun x => C₁ x && C₂ x) := by
  induction R with
  | nil => simp
  | cons a t ih =>
    simp [List.filter]
    split <;> simp_all [Bool.and_comm]
```

또는 Mathlib의 `List.filter_filter`를 사용:

```lean
theorem select_compose' {α : Type} (R : List α) (C₁ C₂ : α → Bool) :
    (R.filter C₂).filter C₁ = R.filter (fun x => C₁ x && C₂ x) := by
  rw [List.filter_filter]
  congr 1
  ext x
  exact Bool.and_comm ..
```
</details>

### 연습 10.2: 선택 연산자의 교환 법칙 (Rosen 연습문제 21)

s_{C₁}(s_{C₂}(R)) = s_{C₂}(s_{C₁}(R))임을 증명하라.

```lean
theorem select_comm {α : Type} (R : List α) (C₁ C₂ : α → Bool) :
    (R.filter C₂).filter C₁ = (R.filter C₁).filter C₂ := by
  sorry
```

<details>
<summary>💡 답 보기</summary>

```lean
theorem select_comm {α : Type} (R : List α) (C₁ C₂ : α → Bool) :
    (R.filter C₂).filter C₁ = (R.filter C₁).filter C₂ := by
  rw [select_compose, select_compose]
  congr 1
  ext x
  exact Bool.and_comm ..
```
</details>

---

## 11. 사용된 Lean 4 전술 · 함수 정리

| 전술/함수 | 용도 | 예시 |
|---------|------|------|
| `structure` | 레코드(구조체) 정의 | `structure Student where name : String ...` |
| `List.filter` | 조건을 만족하는 원소만 필터링 | `db.filter (fun r => r.major == "CS")` |
| `List.map` | 각 원소에 함수 적용 | `db.map (fun r => r.name)` |
| `List.flatMap` | map + flatten (결합에 사용) | `ts.flatMap fun t => ...` |
| `deriving Repr` | `#eval`로 출력 가능하게 | `structure Foo ... deriving Repr` |
| `deriving DecidableEq` | `==` 비교 가능하게 | 조건 판정에 필요 |
| `Set.mem_setOf_eq` | 집합 소속 정의 펼침 | `simp [Set.mem_setOf_eq]` |
| `norm_num` | 수치 계산 자동 증명 | `2 + 3 = 5` |
| `omega` | 자연수/정수 산술 | `¬ (1 + 1 = 3)` |

---

## 12. 핵심 요약

1. **n항 관계**(n-ary relation)는 n개 집합의 카르테시안 곱의 부분집합이다. 차수(degree)는 n이다.
2. **관계 데이터베이스**는 n항 관계로 데이터를 저장하며, 테이블·레코드·필드 개념으로 구성된다.
3. **기본 키**(primary key)는 레코드를 유일하게 식별하는 속성이고, **합성 키**(composite key)는 여러 속성의 조합이다.
4. **선택 연산자**(selection operator)는 조건을 만족하는 레코드를 필터링한다 → Lean 4의 `List.filter`.
5. **투사**(projection)는 관심 있는 필드만 남기고 나머지를 삭제한다 → Lean 4의 `List.map`.
6. **결합**(join)은 공유 필드를 기준으로 두 테이블을 합친다 → Lean 4의 `List.flatMap` + `filter`.
7. SQL의 SELECT는 투사, WHERE는 선택, FROM은 결합에 대응한다.
8. **연관 법칙**의 지지도(support)와 신뢰도(confidence)는 데이터마이닝의 기본 척도이다.

---

> **다음 파트 예고**: Part 12-D에서는 **관계의 표현** (Section 9.3)을 다룬다. 관계를 **행렬**(matrix)과 **방향성 그래프**(directed graph)로 표현하는 방법을 배우고, 행렬의 부울 곱을 이용하여 관계의 합성을 계산한다!
