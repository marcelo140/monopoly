open util/ordering[State]

sig State {}

abstract sig Type {}

sig Service extends Type {}

sig Color extends Type {}

sig Property {
	type: one Type
}

abstract sig Building {}

sig Hotel extends Building {}

sig House extends Building {}

sig Player {
	players: set State,
	properties: Property -> State,
	houses: Property -> House -> State,
	hotels: Property -> Hotel -> State
}



fact {
	let buildings = houses+hotels | all s: State {
		-- Uma propriedade pode ter apenas um hotel
		Player.hotels.s in Property -> lone Hotel

		-- As propriedades pertencem a apenas um jogador, o qual deve ainda estar em jogo
		properties.s in players.s lone -> Property                      

		-- Tanto as casas como os hóteis pertencem apenas a uma propriedade 
		Player.buildings.s in Property lone -> Building 

		-- Apenas propriedades com cor (não são serviços) podem ter edifícios
		all b: Building, pr: Property |
			pr->b in Player.buildings.s => pr.type in Color
	
		-- Se um jogador tem um edifício numa propriedade, então tem todas as propriedades daquela cor 
		all p: Player, pr: Color.~type |
			pr in p.buildings.s.Building => pr.type.~type in p.properties.s

		all pr: Property {
			-- Nenhuma propriedade tem mais de 4 casas
			lte[#(Player.houses.s[pr]), 4]                  

			-- Se uma propriedade tem um hotel, não tem casas
			some Player.hotels.s[pr] => no Player.houses.s[pr]
		}

		all pr: Color.~type | all other: pr.type.~type - pr {
			-- Para duas propriedades da mesma cor, se nenhuma tem um hotel, então a diferença entre o número de casas tem de ser
			-- inferior a 1.
			no Player.hotels.s[pr+other] => lte[minus[#(Player.houses.s[pr]), #(Player.houses.s[other])], 1]

			-- Para duas propriedades da mesma cor, se uma delas tem um hotel, ou a outra tem também um hotel ou tem 4 casas
			some Player.hotels.s[pr] => some Player.hotels.s[other] or eq[#(Player.houses.s[other]), 4]
		 }
	}
}

pred acquire_property[s,s': State, p: Player, pr: Property] {
	pr not in p.properties.s

	properties.s' = properties.s + p->pr

	houses.s' = houses.s
	hotels.s' = hotels.s
	players.s' = players.s
}

pred acquire_house[s,s': State, p: Player, pr: Property] {
	some h: House - Property.(Player.houses.s) | 
		houses.s' = houses.s + p->pr->h

	properties.s' = properties.s
	hotels.s' = hotels.s
	players.s' = players.s
}

pred sell_house[s,s': State, p: Player, pr: Property] {
	some h: p.houses.s[pr] |
		houses.s' = houses.s - p->pr->h

	properties.s' = properties.s
	hotels.s' = hotels.s
	players.s' = players.s
}

pred acquire_hotel[s,s': State, p: Player, pr: Property] {
	eq[#(p.houses.s[pr]), 4]

	houses.s' = houses.s - p->pr->House
	some h: Hotel - Property.(Player.hotels.s) | 
		hotels.s' = hotels.s + p->pr->h

	properties.s' = properties.s
	players.s' = players.s
}

pred sell_hotel[s, s': State, p: Player, pr: Property] {
	pr in p.hotels.s.Hotel

	hotels.s' = hotels.s - p->pr->Hotel
	some disj h1,h2,h3,h4:House | houses.s' = houses.s + p->pr->(h1+h2+h3+h4)

	properties.s' = properties.s
	players.s' = players.s	
}

pred trade_property[s,s': State, p1,p2: Player, pr: Property] {
	pr in p1.properties.s
	no p1 & p2

	p1.properties.s' = p1.properties.s - pr
	p2.properties.s' = p2.properties.s + pr

	all p: Player - (p1+p2) | p.properties.s' = p.properties.s
	houses.s' = houses.s
	hotels.s' = hotels.s
	players.s' = players.s
}

pred lose[s, s': State, p: Player] {
	gt[#(players.s), 1]
	p in players.s

	players.s' = players.s - p
	properties.s' = properties.s - p->Property
	hotels.s' = hotels.s - p->Property->Hotel
	houses.s' = houses.s - p->Property->House
}

run acquire_property_is_consistent {
	some s: State, p: Player, pr: Property | acquire_property[s, s.next, p, pr]
} for 3 but 2 State, 1 Player

run acquire_house_is_consistent {
	some s: State, p: Player, pr: Property | acquire_house[s, s.next, p, pr]
} for 3 but 2 State, 1 Player, 7 Building

run sell_house_is_consistent {
	some s: State, p: Player, pr: Property | sell_house[s, s.next, p, pr]
} for 3 but 2 State

run acquire_hotel_is_consistent {
	some s: State, p: Player, pr: Property | acquire_hotel[s, s.next, p, pr]
} for 2 but 1 Player, 9 Building, exactly 8 House, 0 Service, 1 Color

run sell_hotel_is_consistent {
	some s: State, p: Player, pr: Property | sell_hotel[s, s.next, p, pr]
}	for 2 but 2 State, 5 Building

run lose_is_consistent {
	some s: State, p: Player | lose[s, s.next, p]
} for 3 but 2 State



assert trade_property_implies_no_buildings {
	all s: State, p1,p2: Player, pr: Property |
		trade_property[s, s.next, p1, p2, pr] => no pr.type.~type & Player.(houses+hotels).s.Building
}

assert cant_sell_house_while_holding_hotel {
	all s: State, pr: Property |
		pr in Player.hotels.s.Hotel and sell_house[s, s.next, pr.~(properties.s), pr] => houses.(s.next) = houses.s
}

assert number_of_players_only_decreases {
	all s: State, p: Player, pr: Property {
		acquire_property[s, s.next, p, pr]
		or
		acquire_house[s, s.next, p, pr] or sell_house[s, s.next, p, pr]
		or
		acquire_hotel[s, s.next, p, pr] or sell_hotel[s, s.next, p, pr] implies players.s = players.(s.next)

		lose[s, s.next, p] implies eq[#(players.(s.next)), minus[#(players.s), 1]]
	}
}

/*
A regra que requer que os edifícios sejam vendidos antes de uma propriedade ser trocada está implícita no facto
de um jogador só poder ter edifícios se tiver todas as propriedades daquela cor.
*/
check trade_property_implies_no_buildings for 3 but 2 State, 2 Player

/*
É impossível vender uma casa enquanto houver um hotel numa das propriedades daquela cor.
*/
check cant_sell_house_while_holding_hotel for 3 but 2 State, 6 Building

/*
O número de jogadores apenas diminui, aproximando-nos do fim do jogo.
*/
check number_of_players_only_decreases for 3 but 2 State, 6 Building
