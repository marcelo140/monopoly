sig Color {}

sig Property {
	color: lone Color
}

sig Player {
	properties: set Property,
	houses: Property -> set House,
	hotels: Property -> lone Hotel
}

abstract sig Building {}

sig Hotel extends Building {}

sig House extends Building {}

fact {
	-- As propriedades pertencem a apenas um jogador
	properties in Player lone -> Property                      

	-- Tanto as casas como os hóteis pertencem apenas a uma propriedade 
	Player.houses + Player.hotels in Property lone -> Building 

	-- Apenas propriedades com cor (não são serviços) podem ter edifícios
	all b: Building | one b.~(Player.(houses+hotels)).color    

	-- Se um jogador tem um edifício numa propriedade, então tem todas as restantes propriedades da mesma cor 
	all p: Player, c: p.(houses+hotels).Building.color |       
		c.~color in p.properties                                 


	all p: Property {
		-- Nenhuma propriedade tem mais de 4 casas
		lte[#(p.(Player.houses)), 4]                  

		-- Se uma propriedade tem um hotel, não tem casas
		some p.(Player.hotels) => no p.(Player.houses)
	}

	all p: Color.~color | all other: p.color.~color - p {
		-- Para duas propriedades da mesma cor, se nenhuma tem um hotel, então a diferença entre o número de casas tem de ser
		-- inferior a 1.
		no (p+other).(Player.hotels) => lte[minus[#(p.(Player.houses)), #(other.(Player.houses))], 1]

		-- Para duas propriedades da mesma cor, se uma delas tem um hotel, ou a outra tem também um hotel, ou tem 3 ou mais casas
		some p.(Player.hotels) => some other.(Player.hotels) or gte[#(other.(Player.houses)), 3]
	}
}

run {}
