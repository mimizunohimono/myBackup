def f
  seed = 10
  rseed = Random.new(seed)
  sum = 0
  for j in 1..10 do
    x = 0
    for i in 1..10 do
      r = Random.new(rseed.rand(100))
      if(r.rand > 0.5) then x = x + 1
      else x = x - 1
      end
    end
    p x
    sum = sum + x
  end
  p sum
end

f
