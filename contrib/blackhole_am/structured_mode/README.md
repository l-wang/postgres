This is a structured task that is recommended for people that want a
more streamlined flow with a predetermined storage medium. A patch is
provided to give minor guidance.

To start, apply the patch provided:
```
git am 0001-Add-helper-notices.patch
```

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

For the INSERT calls, you'll need to store the input values in some
form of storage. Simply use a FILE implementation using the stdio
library.  So for example, the above `foo` table may simply exist on
disk as such:
```
○ → cat /tmp/blackhole_am_16402
42
1
23
```

Optionally, try making DELETE and UPDATE work as well. If those are
done, try getting snapshots and/or WHERE filtering to work.

For your convenience, the above example is written as a pg_regress
test which can be invoked via:
```
make check
```

Good luck!
