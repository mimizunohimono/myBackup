.print "--Q1"
select s.sname
from Student as s
where s.standing = "JR"
and s.snum in (
    select e.snum
    from Enrolled as e
    where e.cname in (
    	  select c.name
	  from Class as c
	  where c.fid in (
	  	select f.fid
		from Faculty as f
		where f.fname = "I. Teach"
		)
	)
);

.print "--Q2"
select max(s.age)
from student s
where s.age in (
      (select s2.age
      from student s2
      where s2.major = "History"),
      (select s3.age
      from student s3
      where s3.snum in (
      	    select e.snum
    	    from Enrolled as e
	    where e.cname in (
    	    	  select c.name
		  from Class as c
		  where c.fid in (
		  	select f.fid
			from Faculty as f
			where f.fname = "I. Teach"
			)
		)
	)
	)
);

.print "--Q3--"
select c.name
from class c
where c.room = "R128"
or c.name in(
   select e.cname
   from enrolled e
   group by e.cname
   having count(*) >= 5
);

.print "--Q4--"

.print "--Q5--"
select f.fname
from faculty f
where f.fid in (
      select c.fid
      from class c
      group by c.name
      having count(*)=(
      	     select count(distinct c.name)
	     from class c
));

.print "--Q6--"

select f.fname
from faculty f
where f.fid in(
      select c.fid
      from class c
      where c.name in(
      	    select e.cname
	    from enrolled e
	    group by e.cname
	    having count(*) < 5
));

.print "--Q7--"
select s.standing, avg(s.age)
from student s
group by s.standing;

.print "--Q8--"
select s.standing, avg(s.age)
from student s
group by s.standing
having not s.standing = "JR";

.print "--Q9--"
select f.fname, count(c.room)
from faculty f left join class c on f.fid = c.fid
where f.fid in (
      select c2.fid
      from class c2
      group by c2.fid
      having c2.fid not in(
      	     select c3.fid
	     from class c3
	     where f.fid = c3.fid and not c3.room = "R128"));

.print "--Q10--"
select s.sname
from student s
where s.snum in(
      select e.snum
      from enrolled e
      group by e.snum
      having count(*) >= (
      	     select max(cnt)
      	     from (
	     	  select count(*) as cnt
	     	  from enrolled e2
		  group by e2.snum
	     	  )
	     )
);

.print "--Q11--"
select s.sname
from student s
where not exists(
      select e.snum
      from enrolled e
      where s.snum = e.snum
);

.print "--Q12--"
