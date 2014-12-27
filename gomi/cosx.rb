def func
  x = 0.0
  20.times do |n|
    x = Math.cos(x)
    p n,x
  end
end

func
