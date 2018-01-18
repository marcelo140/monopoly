open util/ordering[State]

sig State {}

sig Color {}

sig Property {
	color: lone Color
}

sig Player {
	properties: Property -> State,
	houses: Property -> House -> State,
	hotels: Property -> Hotel -> State
}

abstract sig Building {}

sig Hotel extends Building {}

sig House extends Building {}

fact {
	all s: State {
		Player.(houses.s) in Property -> set House
		Player.(hotels.s) in Property -> lone Hotel

		-- As propriedades pertencem a apenas um jogador
		properties.s in Player lone -> Property                      

		-- Tanto as casas como os hóteis pertencem apenas a uma propriedade 
		Player.(houses.s) + Player.(hotels.s) in Property lone -> Building 

		-- Apenas propriedades com cor (não são serviços) podem ter edifícios
		all b: Building | one b.~(Player.(houses.s+hotels.s)).color    

		-- Se um jogador tem um edifício numa propriedade, então tem todas as restantes propriedades da mesma cor 
		all p: Player, c: p.(houses.s+hotels.s).Building.color |       
			c.~color in p.properties.s                              

		all p: Property {
			-- Nenhuma propriedade tem mais de 4 casas
			lte[#(p.(Player.houses.s)), 4]                  

			-- Se uma propriedade tem um hotel, não tem casas
			some p.(Player.hotels.s) => no p.(Player.houses.s)
		}

		all p: Color.~color | all other: p.color.~color - p {
			-- Para duas propriedades da mesma cor, se nenhuma tem um hotel, então a diferença entre o número de casas tem de ser
			-- inferior a 1.
			no (p+other).(Player.hotels.s) => lte[minus[#(p.(Player.houses.s)), #(other.(Player.houses.s))], 1]

			-- Para duas propriedades da mesma cor, se uma delas tem um hotel, ou a outra tem também um hotel, ou tem 3 ou mais casas
			some p.(Player.hotels.s) => some other.(Player.hotels.s) or gte[#(other.(Player.houses.s)), 3]
		}
	}
}

run {} for 3 but exactly 1 Player, 7 Building
