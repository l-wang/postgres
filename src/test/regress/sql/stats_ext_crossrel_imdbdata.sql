-- Join MCV statistics tests

--
-- Note: tables for which we check estimated row counts should be created
-- with autovacuum_enabled = off, so that we don't have unstable results
-- from auto-analyze happening when we didn't expect it.
--

-- directory paths are passed to us in environment variables
\getenv abs_srcdir PG_ABS_SRCDIR

-- prepare some test data
CREATE TABLE keyword (
    id integer NOT NULL PRIMARY KEY,
    keyword text NOT NULL,
    phonetic_code character varying(5)
);

CREATE TABLE movie_keyword (
    id integer NOT NULL PRIMARY KEY,
    movie_id integer NOT NULL,
    keyword_id integer NOT NULL
);

\set keyword_filename :abs_srcdir '/data/keyword.csv'
COPY keyword FROM :'keyword_filename' DELIMITER ',' CSV NULL '' ESCAPE '\' HEADER;
\set movie_keyword_filename :abs_srcdir '/data/movie_keyword.csv'
COPY movie_keyword FROM :'movie_keyword_filename' DELIMITER ',' CSV NULL '' ESCAPE '\' HEADER;

select id from keyword EXCEPT select keyword_id from movie_keyword;
select keyword_id from movie_keyword EXCEPT select id from keyword;

-- delete the orphaned keyword_id in movie_keyword (just so that we can create a foreign key)
DELETE FROM movie_keyword WHERE keyword_id NOT IN (SELECT id FROM keyword);
ALTER TABLE movie_keyword ADD CONSTRAINT movie_keyword_keyword_id_fkey FOREIGN KEY (keyword_id) REFERENCES keyword(id) ON DELETE CASCADE;

CREATE INDEX keyword_id_movie_keyword ON movie_keyword(keyword_id);

SET default_statistics_target = 10000;
ANALYZE keyword;
ANALYZE movie_keyword;

SELECT k.keyword, COUNT(*) as movie_count
FROM keyword k, movie_keyword mk
WHERE k.keyword IN ('sequel',
                    'fight',
                    'violence')
  AND k.id = mk.keyword_id
GROUP BY k.keyword
ORDER BY movie_count DESC;

-- w/o join MCV statistics, planner would use a nested loop join
EXPLAIN (verbose, costs off)
SELECT * FROM keyword k, movie_keyword mk WHERE k.keyword IN ('superhero',
                                                              'sequel',
                                                              'based-on-comic',
                                                              'fight',
                                                              'violence') AND k.id = mk.keyword_id;

-- Creating a dependency relationship on keyword.id and keyword.keyword
CREATE STATISTICS keyword_stats ON keyword, id FROM keyword;
ANALYZE keyword;
SELECT stxname, stxkeys, stxddependencies FROM pg_statistic_ext join pg_statistic_ext_data on (oid = stxoid) WHERE stxname = 'keyword_stats';

-- Implicitly create the join MCV statistics on keyword.keyword and movie_keyword.keyword_id
ANALYZE movie_keyword;

-- w/ join MCV statistics, planner would use a hash join
EXPLAIN (verbose,costs off)
SELECT * FROM keyword k, movie_keyword mk WHERE k.keyword IN ('superhero',
                                                              'sequel',
                                                              'based-on-comic',
                                                              'fight',
                                                              'violence') AND k.id = mk.keyword_id;
RESET default_statistics_target;
