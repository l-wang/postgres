This is an unstructured task for people that are confident in their
Postgres internals knowledge and/or C skills. The user is free to use
any storage medium and the task as they'd like.

Your task is to modify this blackhole_am contrib module to make the
following three queries work:
1. CREATE TABLE
2. INSERT
3. SELECT

So for example, something like this should be expected at the end:
```
postgres=# CREATE TABLE foo (a int) USING blackhole_am;
CREATE TABLE
postgres=# SELECT * FROM foo;
 a
---
(0 rows)

postgres=# INSERT INTO foo VALUES (42);
INSERT 0 1
postgres=# SELECT * FROM foo;
 a
----
 42
(1 row)

postgres=# INSERT INTO foo VALUES (1), (23);
INSERT 0 2
postgres=# SELECT * FROM foo;
 a
----
 42
  1
 23
(3 rows)
```

Store the input values from the INSERT calls in any storage medium you
prefer and in any format (e.g. as just plain strings in a FILE or in
an actual optimized format).

Optionally, try making DELETE and UPDATE work as well. If those are
done, try getting snapshots and/or WHERE filtering to work.

For your convenience, the above example is written as a pg_regress
test which can be invoked via:
```
make check
```

Good luck!
