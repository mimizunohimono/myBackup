#!/usr/bin/ruby
def mod(a, b)
  aa = a
  while aa > b
    aa = aa - b
  end
  return aa
end

def euclid(a, b)
  x1 = 1
  y1 = 0
  z1 = a
  x2 = 0
  y2 = 1
  z2 = b

  while(z2 != 1) do
    break if z2 == 0
    q = (z1 - (z1 % z2)) / z2    
    x1 = x1 - (q*x2)
    y1 = y1 - (q*y2)
    z1 = z1 - (q*z2)
    x1, x2 = x2, x1
    y1, y2 = y2, y1
    z1, z2 = z2, z1
  end
  
  if x2 < 0
    return x2 + b
  else return x2
  end
end

def powmod(a, k, p)
  kd = k
  ans = 1
  apow = a
  while kd != 0
    if kd & 1 == 1
      then ans = (ans*apow)%p
      kd = kd - 1
    end
    apow = (apow*apow)%p
    kd = kd / 2
  end
  return ans
end

n = 1517330236262917595314610888889322115651087080826711948897066340883208205571592392362650858571076247939805436226544833224526137582834770402681005343930059463684528957271778199162575053306238099823295117697031968370690372250916935800738698142103275969223264184374648246277564306900886005299731265812255274723175925185522344831066577166867786835955092059346244885587228196357297758371381557924676260190209536670230008561217008649261974735505203813478978893582292682827884118215872470401293272325715864815977064075988643101088355047954735427424641386870772845440782632933485165110172437511822736907550777817722248753671107339823410418938404382732079381329288400012929311347390423061254658780185245562668131009832293474920208834795460061115101364091252176594144096675899952570380792978037217747311595899301451192342027799533264325948876556110474850761538179748318187805312451895898751337975457949549497666542175077894987697085521882531938339334715190663665300179658557458036053188152532948734992896239950564081581184284728802682982779186068791931259198917308153082917381616147108543673346682338045309449569430550618884202465809290850964525390539782080230737593560891353558335337408957948041667929154230334506735825418239563481028126435029

p = 34111525225922333955113751419357677129436029651245533697825114748126342624744832960936498161825269430327019858323450578875242014583535842110912370431931233957939950911741013017595977471949767235426490850284286661592357779825212265055931705799916913817655743434497422993498931394618832741336247426815710164342599150990608143637331068220244525541794855651643135012846039439355101027994945120698530177329829213208761057392236875366458197098507252851244132455996468628957560178868724310000317011912994632328371761486669358065577269198065792981537378448324923622959249447066754504943097391628716371245206444816309511381323

q = 44481453884385518268018625442920628989497457642625668259648790876723318635861137128631112417617317160816537010595885992856520476731882382742220627466006460645416066646852266992087386855491152795237153901319521506429873434336969666536995399866125781057768075533560120399184566956433129854995464893265403724034960689938351450709950699740508459206785093693277541785285699733873530541918483842122691276322286810422297015782658645129421043160749040846216892671031156465364652681036828461619272427318758098538927727392459501761203842363017121432657534770898181975532066012149902177196510416802134121754859407938165610800223

c = 225549592628492616152632265482125315868911125659971085929712296366214355608049224179339757637982541542745010822022226409126123627804953064072055667012172681551500780763483172914389813057444669314726404135978565446282309019729994976815925850916487257699707478206132474710963752590399332920672607440793116387051071191919835316845827838287954541558777355864714782464299278036910958484272003656702623646042688124964364376687297742060363382322519436200343894901785951095760714894439233966409337996138592489997024933882003852590408577812535049335652212448474376457015077047529818315877549614859586475504070051201054704954654093482056493092930700787890579346065916834434739980791402216175555075896066616519150164831990626727591876115821219941268309678240872298029611746575376322733311657394502859852213595389607239431585120943268774679785316133478171225719729917877009624611286702010936951705160870997184123775488592130586606070277173392647225589257616518666852404878425355285270687131724258281902727717116041282358028398978152480549468694659695121115046850718180640407034795656480263573773381753855724693739080045739160297875306923958599742379878734638341856117533253251168244471273520476474579680250862738227337561115160603373096699944163

e = 65537
p_1q_1 = (p - 1)*(q - 1)
d = euclid(e, p_1q_1)
p m = powmod(c, d, n)
