from sets import Set
#import global_variables
from pprint import pprint
from collections import OrderedDict
import re
import random
class DomainInfoFormatting():
	def __init__(self):

		self.init_file_names()
		self.init_files_markers()

		self.refined_sorts_hierarchy_dic = OrderedDict()
		self.abstract_1_sorts_lines = []
		self.abstract_1_attributes_lines = []
		is_abstract_1_sorts_line = False
		is_abstract_1_attributes_line = False
		with open(self.domain_info_file) as f:
			for line in f:
				line = line.strip()
				if line == '%% Abstraction_1 Sorts':
					is_abstract_1_sorts_line = True
					continue
				elif line == '%% End of Abstraction_1 Sorts':
					is_abstract_1_sorts_line = False
					continue
				elif line == '%% Abstraction_1 Attributes':
					is_refined_attributes_line = True
					continue
				elif line == '%% End of Abstraction_1 Attributes':
					is_abstract_1_attributes_line = False
					continue
				elif 'max_number_steps_ToI_planning' in line:
					self.max_number_steps_ToI_planning = int(re.search(r'\d+', line).group()) #get the integer in the line

				if is_abstract_1_sorts_line:
					self.abstract_1_sorts_lines.append(line)
					if '#' not in line: continue
					line_split = line.replace(' ','').strip('.').split('=')
					sort_name = line_split[0]
					sort_composition_string = line_split[1]
					sort_composition_list = sort_composition_string.split('+')
					if '{' in sort_composition_list[0] or sort_composition_list[0] in self.refined_sorts_hierarchy_dic.keys():
						sort_composition_set = Set([v for v in sort_composition_list if v in self.refined_sorts_hierarchy_dic.keys()])
						for v in sort_composition_list:
							 if '{' in v: sort_composition_set.update(Set(v.strip('{}').split(',')))
						self.refined_sorts_hierarchy_dic[sort_name] = sort_composition_set
					elif '(' in sort_composition_list[0] or sort_composition_list[0] in self.refined_sorts_hierarchy_dic.keys():
						sort_composition_set = Set([v for v in sort_composition_list if v in self.refined_sorts_hierarchy_dic.keys()])
						for v in sort_composition_list:
							if '(' in v:
								v = v.strip(')').split('(')
								self.refined_sorts_hierarchy_dic[v[0]] = v[1].split(',')
								sort_composition_set.add(v[0])
						self.refined_sorts_hierarchy_dic[sort_name] = sort_composition_set

				if is_abstract_1_attributes_line: self.abstract_1_attributes_lines.append(line)


		self.refined_constants = Set()
		for values in self.refined_sorts_hierarchy_dic.values(): self.refined_constants.update(Set([v for v in values if v not in self.refined_sorts_hierarchy_dic.keys()]))

		self.functions = Set([v for v in self.refined_sorts_hierarchy_dic.keys() if '#' not in v  and v not in self.refined_constants])

		self.dic_action_paramters = {}

		self.abstract_executability_conditions = ['impossible(move(R, L), I) :- holds(loc(R, L), I).',
      		'impossible(move(R, L2), I) :- holds(loc(R, L1), I), -next_to(L1, L2).',
      		'impossible(move(R, L), I) :-  -holds(lift_door_open(L, C), I), holds(loc(R, C), I).',
      		'impossible(move(R, C), I) :-  -holds(lift_door_open(L, C), I), holds(loc(R, L), I).',
      		'impossible(pickup(R, O1), I) :- holds(in_hand(R, O2), I).',
      		'impossible(pickup(R, O), I) :- holds(loc(R, L), I), not holds(loc(O, L), I).',
      		'impossible(call_lift(R, L, C), I) :- not holds(loc(R, C), I).',
      		'impossible(call_lift(R,L,C), I) :- not next_to(L,C).',
      		'impossible(request_move(R, L, C), I) :- not holds(loc(R, L), I).',
      		'impossible(put_on_shelf(R, O, S), I) :- -holds(in_hand(R,O), I).',
      		'impossible(put_on_shelf(R, O, S), I) :- -holds(loc(R,L), I), in_room(S,L).',
      		'impossible(exo_move(O,L), I) :- holds(in_hand(R, O), I).',
      		'impossible(exo_move(R, L), I) :- holds(loc(R, L), I).']
		# the next dictionary holds actions as a keys (without paramters) and as values a tuple consisting of
		# 1. the variables used by this actions as paramteres, and
		# 2. all fluents used in all the executability conditions relevant to that action as value.
		self.actions_param_and_exec_conditions_dic = self.get_dic_action_variables_conditions(self.abstract_executability_conditions)

		'''
		self.init_extra_ASP_strings()
		self.reg_exp_sorts = r'#*\w*_*\w*' #regular expression that helps find the sorts in the asp text. The regular expression represents words composed with letters and numbers, possibley with # at the beginning, and possible with a _ in between its letters.

		self.refined_sorts_hierarchy_dic = OrderedDict()
		self.components_dic = OrderedDict()

		self.abstract_sorts_lines = []
		self.refined_sorts_lines = []
		self.abstract_attributes_lines = []
		self.refined_attributes_lines = []

 		#using line flags when reading domain info file.
		is_abstract_sorts_line = False
		is_refined_sorts_line = False
		is_abstract_attributes_line = False
		is_refined_attributes_line = False

		with open(self.domain_info_file) as f:
			for line in f:
				line = line.strip()
				if line == '%% Refined Sorts':
					is_refined_sorts_line = True
					continue
				elif line == '%% Refined Attributes':
					is_refined_attributes_line = True
					continue
				elif line == '%% End of Refined Sorts':
					is_refined_sorts_line = False
					continue
				elif line == '%% End of Refined Attributes':
					is_refined_attributes_line = False
					continue
				elif line == '%% End of Abstract Sorts':
					is_abstract_sorts_line = False
					continue
				elif line == '%% End of Abstract Attributes':
					is_abstract_attributes_line = False
					continue
				elif line == '%% Abstract Sorts':
					is_is_abstract_sorts_line = True
					continue
				elif line == '%% Abstract Attributes':
					is_abstract_attributes_line = True
					continue
				elif 'max_number_steps_ToI_planning' in line:
					self.max_number_steps_ToI_planning = int(re.search(r'\d+', line).group()) #get the integer in the line
				elif 'max_number_steps_refined_planning' in line:
					self.max_number_steps_refined_planning = int(re.search(r'\d+', line).group()) #get the integer in the line

				if is_refined_sorts_line:
					self.refined_sorts_lines.append(line)
					if '#' not in line: continue
					line_split = line.replace(' ','').strip('.').split('=')
					sort_name = line_split[0]
					sort_composition_string = line_split[1]
					sort_composition_list = sort_composition_string.split('+')
					if '{' in sort_composition_list[0] or sort_composition_list[0] in self.refined_sorts_hierarchy_dic.keys():
						sort_composition_set = Set([v for v in sort_composition_list if v in self.refined_sorts_hierarchy_dic.keys()])
						for v in sort_composition_list:
							 if '{' in v: sort_composition_set.update(Set(v.strip('{}').split(',')))
						self.refined_sorts_hierarchy_dic[sort_name] = sort_composition_set
					elif '(' in sort_composition_list[0] or sort_composition_list[0] in self.refined_sorts_hierarchy_dic.keys():
						sort_composition_set = Set([v for v in sort_composition_list if v in self.refined_sorts_hierarchy_dic.keys()])
						for v in sort_composition_list:
							if '(' in v:
								v = v.strip(')').split('(')
								self.refined_sorts_hierarchy_dic[v[0]] = v[1].split(',')
								sort_composition_set.add(v[0])
						self.refined_sorts_hierarchy_dic[sort_name] = sort_composition_set

				if is_refined_attributes_line:
					self.refined_attributes_lines.append(line)
					if(line[:5] =='comp('):
						line_split = line.replace(' ','').replace('comp(','').strip(').').split(',')
						self.components_dic[line_split[0]] = line_split[1]
				if is_abstract_sorts_line: self.abstract_sorts_lines.append(line)
				if is_abstract_attributes_line: self.abstract_attributes_lines.append(line)

		self.refined_constants = Set()
		for values in self.refined_sorts_hierarchy_dic.values(): self.refined_constants.update(Set([v for v in values if v not in self.refined_sorts_hierarchy_dic.keys()]))


		self.refined_constants_sorts_dic = {k:v for k,v in self.refined_sorts_hierarchy_dic.items() if Set(v).issubset(self.refined_constants)}
		self.abstract_constants_sorts_dic = {k.replace('coarse_',''):v for k,v in self.refined_constants_sorts_dic.items() if 'coarse_' in k}
		self.refined_constants_sorts_dic = {k:v for k,v in self.refined_constants_sorts_dic.items() if 'coarse_' not in k}
		self.abstract_constants_lines = [k + ' = ' + '{' + ', '.join(v) + '}.' for k,v in self.abstract_constants_sorts_dic.items()]
		self.refined_constants_lines = [k + ' = ' + '{' + ', '.join(v) + '}.' for k,v in self.refined_constants_sorts_dic.items()]

		self.abstract_executability_conditions = ['-occurs(move(R, L), I) :- holds(loc(R, L), I).',
												'-occurs(move(R, L2), I) :- holds(loc(R, L), I), -next_to(L,L2).',
												'-occurs(put_down(R, O), I) :-  -holds(in_hand(R, O), I).',
												'-occurs(pickup(R, O1), I) :- holds(in_hand(R, O2), I).',
												'-occurs(pickup(R, O), I) :- holds(loc(R, L), I), not holds(loc(O, L), I).',
												'-occurs(exo_move(O,L),I) :- holds(loc(O,L),I).',
												'-occurs(exo_move(O,L),I) :- holds(in_hand(R,O),I).']
		# the next dictionary holds actions as a keys (without paramters) and as values a tuple consisting of
		# 1. the variables used by this actions as paramteres, and
		# 2. all fluents used in all the executability conditions relevant to that action as value.
		self.actions_param_and_exec_conditions_dic = self.get_dic_action_variables_conditions(self.abstract_executability_conditions)

		self.refined_world_causal_law = '-holds(in_hand(R,OP2),I+1) :- occurs(put_down(rob,OP1),I), comp(OP1,B), comp(OP2,B), holds(coarse_in_hand(rob,B),I).'
		self.inferring_indirect_observations_display_string = 'holds(indirectly_observed(rob,B,C),numSteps).'
		self.refined_world_display_string = 'holds(loc(A,B),numSteps).\nholds(in_hand(A,B),numSteps).\nholds(coarse_loc(A,B),numSteps).\nholds(coarse_in_hand(A,B),numSteps).\n'
		self.new_refined_world_executability_condition = '-occurs(put_down(R,OP),I) :- comp(OP,B), -holds(coarse_in_hand(rob,B),I).'
		self.old_refined_world_executability_condition = '-occurs(put_down(R, OP), I) :-  -holds(in_hand(R, OP), I).'

	 	self.create_pre_ASP_refined_world()
		self.create_pre_ASP_inferring_indirect_observations()
		self.create_pre_ASP_refined_planning()
		'''

	'''
	this fuctions gets a sort as string as a paramter, for example '#thing', and returns
	all basic sorts that belong to the set of #thing which are, in this case, 'rob', 'book1' and 'book2'.
	'''
	def get_all_constant_subsorts(self,sort):
		if sort in self.refined_constants: return sort
		my_subsorts = self.refined_sorts_hierarchy_dic[sort]
		my_constant_subsorts = my_subsorts & self.refined_constants
		not_constant_sorts = my_subsorts - my_constant_subsorts
		for s in not_constant_sorts: my_constant_subsorts.update(self.get_all_constant_subsorts(s))
		return my_constant_subsorts

	def get_all_function_subsorts(self,sort):
		if sort in self.functions: return sort
		my_subsorts = self.refined_sorts_hierarchy_dic[sort]
		my_function_subsorts = my_subsorts & self.functions
		not_function_sorts = my_subsorts - my_function_subsorts
		for s in not_function_sorts: my_function_subsorts.update(self.get_all_function_subsorts(s))
		return my_function_subsorts


	def dic_state_to_obs_list(self,dic_state,step):
		return self.holds_to_obs_list(self.dic_state_to_holds_list(dic_state,step))

	def dic_state_to_holds_list(self,dic_state,step):
		robot_name = list(self.get_all_constant_subsorts('#robot'))[0]
		obsList = ['holds('+','.join([v for v in [a,b] if v])+'),'+str(step)+').' for a,b in dic_state.items()]
		for object in self.get_all_constant_subsorts('#object'):
			if 'on_shelf('+object not in dic_state.keys(): obsList.append('-holds(on_some_shelf('+object+'),' +str(step) + ').')
		if [v for v in dic_state.keys() if 'in_hand' in v] == []:
			obsList = obsList + ['-holds(in_hand('+robot_name+','+ object +'),'+ str(step) +').' for object in self.get_all_constant_subsorts('#object')]
		if [v for v in dic_state.keys() if 'lift_door_open' in v] == []:
			obsList = obsList + ['-holds(lift_door_open(lift,'+ corridor +'),'+ str(step) +').' for corridor in self.get_all_constant_subsorts('#corridor')]
		return obsList


	def holds_to_obs_list(self,holds_strings):
		initial_obs_strings = [v.replace('holds','obs').replace('),','),true,') if '-' not in v else v.replace('-holds','obs').replace('),','),false,')  for v in holds_strings]
		return initial_obs_strings


	'''
	def create_relevant_refined_sorts_lines(self,relevant_refined_sorts_hierarchy_dic):
		lines = []
		for sort in relevant_refined_sorts_hierarchy_dic.keys():
			if '#' in sort:
				values = relevant_refined_sorts_hierarchy_dic[sort]
				sorts = [v for v in values if '#' in v]
				functions = [v for v in values if '#' not in v and v in relevant_refined_sorts_hierarchy_dic.keys()]
				constants = [v for v in values if '#' not in v and v not in relevant_refined_sorts_hierarchy_dic.keys()]
				string_split = []
				if constants:
					string_split.append('{' + ','.join(constants) + '}')
				if functions:
					functions_strings = []
					for f in functions:
						functions_strings.append(f+'('+ ','.join(relevant_refined_sorts_hierarchy_dic[f]) +')')
					string_split.append(' + '.join(functions_strings))
				if sorts:
					string_split.append(' + '.join(sorts))
				line = sort + ' = ' + ' + '.join(string_split) + '.'
				lines.append(line)

		return lines
	'''


	# this functions takes a list of strings of the form '-occurs(move(R, L2), I) :- holds(loc(R, L1), I), -next_to(L1,L2).'
	# as input and returns a dictionary where each key represents an action witout its parameters
	# (which are in the left side of the input strings) 'move' in our example, and the values of the dictionary are
	# tuples of 1. a list of the variables used as parameters in the corresponding key-action,
	# and 2. the timless (without the last time step variable) conditions corresponding to the action, using the updated variable names e.g: 'holds(loc(T,K)'
	# It is important to note that in the input, the same action may be using different variables in different conditions.
	# This functions choses variable names not used in the given list and changes the variable names to make sure they are the same.
	def get_dic_action_variables_conditions(self,myListOfConditions):
		#find used uppercase letters:
		usedVariableLetters = Set()
		for s in myListOfConditions:
			for c in s:
				if c.isupper(): usedVariableLetters.add(c)
		dic_action_conditions = {}
		dic_action_variables = {}
		dic_action_variables_conditions = {}
		for condition_line in myListOfConditions:
			condition_split = condition_line.replace(' ','').split(':-')
			action_string= condition_split[0]
			conditions_string = condition_split[1]
			# create the set of fluents that appear in this condition string
			conditions_set = Set()
			holds_indexes = [m.start() for m in re.finditer('holds', conditions_string)]
			for index in holds_indexes:
				precondition = ''
				if index > 0 and conditions_string[index-1] ==  '-': precondition = '-'
				condition = conditions_string[index : conditions_string.find(')',index)+1]
				conditions_set.add(precondition+condition)

			#get the action (without paramters)
			action_with_parameters = action_string[action_string.find('(')+1: action_string.rfind('),')+1]
			action_split = action_with_parameters.split('(')
			action = action_split[0]

			#get the variable names used as paramteres in the action
			this_entry_parameters = action_split[1].replace(')','').split(',')

			# if we have not chosen variable names for the paramters of this action already,
			# choose them and create entry in the dictionaries
			if action not in dic_action_variables:
				chosen_parameters = []
				for i in range(len(this_entry_parameters)):
					upparcaseLetters = Set(map(chr, range(65, 91)))
					p = random.choice(list(upparcaseLetters - usedVariableLetters))
					chosen_parameters.append(p)
					usedVariableLetters.add(p)
				dic_action_variables[action] = chosen_parameters
				dic_action_conditions[action] = Set()

			#replace each parameter in the set of conditions with the new chosen variable names
			chosen_parameters = dic_action_variables[action]
			for old, new in zip(this_entry_parameters,chosen_parameters):
					conditions_set = Set(self.replace_parameter_in_conditions_list(old,new,list(conditions_set)))

			#add conditions to the value set of action_condtions of the corresponding action
			dic_action_conditions[action].update(conditions_set)

		# create one dictionary that contains actions as the keys and tuples with 1.list of chosen parameters and
		# 2.set of fluents as values.
		for k in dic_action_variables:
			dic_action_variables_conditions[k] = (dic_action_variables[k],dic_action_conditions[k])

	# this functions takes two strings A and B  and a list of conditions of the form 'holds(loc(R,B)' as input
	# it replaces the paramter A with the value B in each fluents and returns the
	# new list of fluents.
	def replace_parameter_in_conditions_list(self,A,B,conditions_list):
		for i in range(len(conditions_list)):
			condition = conditions_list[i]
			condition_head	= ''
			if 'holds' in condition:
				condition_head = condition[:condition.find('(')+1]
				fluent = self.get_fluent(condition)
			else: fluent = condition
			fluent_split = fluent.split('(')
			fluent_name = fluent_split[0]
			fluent_parameters = fluent_split[1].replace(')','').split(',')
			for j in range(len(fluent_parameters)):
				if fluent_parameters[j] == A: fluent_parameters[j] = B
			conditions_list[i] = condition_head+fluent_name + '('+ ','.join(fluent_parameters)+')'
		return conditions_list



	# it returns the list of paramterers in the fluent that has been given as input.
	def get_parameters(self,fluent):
		return fluent[fluent.find('(')+1:fluent.find(')')].split(',')


	# it returns the fluent that is part of the 'holds' string that has been given as input
	# for example get_fluent('holds(loc(rob,kitchen),0)' will return 'loc(rob,kitchen)')
	def get_fluent(set,holds_string):
		return holds_string[holds_string.find('(')+1:holds_string.find(')')+1]

	'''
	#this function takes a string 'fluent', a string 'value' and an integer 'index' as input.
	# it then replaces the parameter number 'index' of the 'fluent' function
	# with the 'value' given as input. It returns the fluent with the new value as a its 'index-th' parameter.
	def add_flunet_value_in_index(self,fluent,value,index):
		fluent_split = fluent.split('(')
		fluent_name = fluent_split[0]
		fluent_parameters = fluent_split[1].replace(')','').split(',')
		fluent_parameters[index] = value
		return fluent_name + '('+ ','.join(fluent_parameters)+')'
	'''
	'''
	# this function takes a string 'fluent' as input and returns a list of all the indexes
	# where this fluent's parameters are not grounded (i.e. indexes where the paramter of the fluent
	# is not an object that can be found in the set of all_obj_consts in the domain.
	def not_grounded_indexes(self,fluent):
		parameters = self.get_parameters(fluent)
		return [i for i in range(len(parameters)) if parameters[i] not in self.refined_constants]
	'''

	'''
 	# this flunction returns a boolean indicating if all the paramters of the fluent given as input
	# are elements of the set of all_obj_consts of the domain.
	def is_fully_grounded(self,condition):
		fluent = condition
		if 'holds' in condition: fluent = self.get_fluent(condition)
		parameters = self.get_parameters(fluent)
		return [o for o in parameters if o not in self.refined_constants] == []
	'''

	'''
	# this function gets a string fluent as input and it will return a list of all
	# possible groundings of this fluent. Note that in the input fluent there may be
	# already some grounded parameters which will not be changed. Only the variables
	# will be replace with possible values and returned.
	def all_possible_groundings(self, conditions_list):
		grounded_conditions_set = Set([c for c in conditions_list if self.is_fully_grounded(self.get_fluent(c))])
		not_grounded_conditions_list = [c for c in conditions_list if c not in grounded_conditions_set]
		for condition in not_grounded_conditions_list:
			condition_head = condition[:condition.find('(')+1]
			fluent = self.get_fluent(condition)
			parameters = self.get_parameters(fluent)
			indexes = self.not_grounded_indexes(fluent)
			for value in self.refined_constants:
				new_condition =  condition_head + self.add_flunet_value_in_index(fluent,value,indexes[0])
				if self.is_fully_grounded(new_condition):
					grounded_conditions_set.add(new_condition)
				else: grounded_conditions_set.update(self.all_possible_groundings([new_condition]))
		return grounded_conditions_set
	'''


	def dic_answerToState(self,answer):
		dic_coarse_state = {}
		answer_split =  answer.rstrip().strip('{').strip('}').split(', ')
		for holds_string in answer_split:
			if '-' in holds_string: continue
			fluent = holds_string[holds_string.find('(')+1:holds_string.rfind(',')]
			fluent_split = (fluent[:-1]).split(',')
			dic_coarse_state[fluent_split[0].encode('ascii', 'ignore')] = fluent_split[1].encode('ascii', 'ignore')
		return dic_coarse_state


	'''
	def dic_abstractStateToAbstractHoldsSet(self,dic_state,step):
		holds_set = Set()
		for key,value in dic_state.iteritems():
			abstract_fluent = key+','+value+')'
			holds_set.add('holds('+abstract_fluent+','+str(step)+').')

		# if we have an object in hand, we return the set of statements.
		object_in_hand = ''
		if 'in_hand(rob' in dic_state: object_in_hand = dic_state['in_hand(rob']

		# if we do not have an object in hand, we include the coarse -holds statements.
		for object in self.refined_sorts_hierarchy_dic['#coarse_object']:
			if object != object_in_hand: holds_set.add('-holds(in_hand(rob,'+ object+'),'+str(step)+').')


		return holds_set
	'''

	'''
	def dic_abstractStateToCoarseHoldsSet(self,dic_state,step):
		holds_set = Set()
		for key,value in dic_state.iteritems():
			abstract_fluent = key+','+value+')'
			holds_set.add('holds(coarse_'+abstract_fluent+','+str(step)+').')
		# if we have an object in hand, we return the set of statements.

		object_in_hand = ''
		if 'in_hand(rob' in dic_state: object_in_hand = dic_state['in_hand(rob']
		# if we do not have an object in hand, we include the coarse -holds statements.
		for object in self.refined_sorts_hierarchy_dic['#coarse_object']:
			if object != object_in_hand: holds_set.add('-holds(coarse_in_hand(rob,'+ object+'),'+str(step)+').')
		return holds_set
	'''

	'''
	def dic_refinedStateToRefinedHoldsSet(self,dic_state,step):
		holds_set = Set()
		for key,value in dic_state.iteritems():
			abstract_fluent = key+','+value+')'
			holds_set.add('holds('+abstract_fluent+','+str(step)+').')
		# if we have an object in hand, we return the set of statements.
		if 'coarse_in_hand(rob' in dic_state or 'in_hand(rob' in dic_state: return holds_set
		# if we do not have an object in hand, we include all the coarse -holds statements.
		for object in self.refined_sorts_hierarchy_dic['#coarse_object']:
			holds_set.add('-holds(coarse_in_hand(rob,'+ object+'),'+str(step)+').')
		return holds_set
	'''

	'''
	# This function takes as input a statement of the form "indirectly_observed(rob,#fluent,#boolean)"
	# and a integer step, and returns and trainsformes it into a statement of the form "obs(#fluent,#boolean,#step)."
	def indirectObservationToObs(self,indirectObservation,step):
		indirectObservation_formatted = indirectObservation.replace('indirectly_observed(rob,coarse_', 'obs(')
		obs = indirectObservation_formatted[:-1]+','+str(step)+').'
		return obs

	# This function takes as input a statement of the form "directly_observed(rob,#fluent,#boolean)"
	# and a integer step, and returns and trainsformes it into a statement of the form "obs(#fluent,#boolean,#step)."
	def directObservationToRefinedObs(self,directObservation,step):
		directObservation_formatted = directObservation.replace('directly_observed(rob,','obs(')
		obs = directObservation_formatted[:-1]+','+str(step)+').'
		return obs
	'''

	'''
	# This function takes a set of constant from the domain as a set of strings and returns an ordered dictionary
	# that contains only the sorts hierarchy (based on the original sorts hierarchy of the domain) that are relevant to the set of constants
	# that have been given as input.
	def infer_relevant_refined_sorts_hierarchy_dic(self, constants):
		relevant_constants_sorts_fluents_actions = Set(constants)

		#keep on adding relevant basic_sorts, functions and function_sorts until
		#no more can be added to the set
		elementsAdded = True
		while elementsAdded:
			adding_again = Set()
			for sort in self.refined_sorts_hierarchy_dic.keys():
				if '#' in sort:
					if len(Set(self.refined_sorts_hierarchy_dic[sort]).intersection(relevant_constants_sorts_fluents_actions)) > 0: adding_again.add(sort)
				else: #it is a function and therefore all values on the dictionary must be part of the set of relevant relevant_constants_sorts_fluents_actions
					if Set(self.refined_sorts_hierarchy_dic[sort]).issubset(relevant_constants_sorts_fluents_actions): adding_again.add(sort)
			length_before = len(relevant_constants_sorts_fluents_actions)
			relevant_constants_sorts_fluents_actions.update(adding_again)
			length_after = len(relevant_constants_sorts_fluents_actions)
			elementsAdded = length_before!=length_after

		relevant_refined_sorts_hierarchy_dic = OrderedDict()
		for sort in self.refined_sorts_hierarchy_dic.keys():
			if sort in relevant_constants_sorts_fluents_actions:
				relevant_refined_sorts_hierarchy_dic[sort] = [x for x in self.refined_sorts_hierarchy_dic[sort] if x in relevant_constants_sorts_fluents_actions]

		return relevant_refined_sorts_hierarchy_dic
	'''

	'''
	def create_pre_ASP_refined_world(self):
		reader = open(self.file_name_pre_ASP_refined_domain, 'r')
		pre_ASP_lines = reader.read().split('\n')
		reader.close()
		pre_ASP_lines[pre_ASP_lines.index(self.sorts_marker)] ='\n'.join(self.refined_sorts_lines)
		pre_ASP_lines[pre_ASP_lines.index(self.attributes_marker)] = '\n'.join(self.refined_attributes_lines)
		pre_ASP_lines[pre_ASP_lines.index(self.causal_law_marker)] = self.refined_world_causal_law
		pre_ASP_lines[pre_ASP_lines.index(self.old_refined_world_executability_condition)] = self.new_refined_world_executability_condition
		pre_ASP_lines.append(self.refined_world_display_string)
		writer = open(self.file_name_pre_ASP_refined_world, 'w')
		writer.write('\n'.join(pre_ASP_lines))
		writer.close()
	'''

	'''
	def create_pre_ASP_inferring_indirect_observations(self):
		reader = open(self.file_name_pre_ASP_refined_domain, 'r')
		pre_ASP_lines = reader.read().split('\n')
		reader.close()
		#removing exo actions
		#for i, line in enumerate(pre_ASP_lines):
		#	if('exo' in line): pre_ASP_lines[i] = '\n'

		#add all attributes
		pre_ASP_lines[pre_ASP_lines.index(self.attributes_marker)] = '\n'.join(self.refined_attributes_lines)
		pre_ASP_lines.append(self.inferring_indirect_observations_display_string)
		writer = open(self.file_name_preASP_inferring_indirect_observations, 'w')
		writer.write('\n'.join(pre_ASP_lines))
		writer.close()
	'''

	'''
	def create_pre_ASP_refined_planning(self):
		reader = open(self.file_name_pre_ASP_refined_domain, 'r')
		pre_ASP_lines = reader.read().split('\n')
		reader.close()
		pre_ASP_lines[0] = '#const numSteps = 5.'
		pre_ASP_lines[pre_ASP_lines.index(self.attributes_marker)] = '\n'.join(self.refined_attributes_lines)
		pre_ASP_lines[ pre_ASP_lines.index(self.planning_marker)] = self.refined_planning_rules_string
		pre_ASP_lines[pre_ASP_lines.index(self.testing_marker)] = self.refined_planning_testing_rules_string
		pre_ASP_lines.append('occurs.')
		#removing exo actions
		pre_ASP_lines = [line for line in pre_ASP_lines if 'exo' not in line]
		writer = open(self.file_name_preASP_refined_planning, 'w')
		writer.write('\n'.join(pre_ASP_lines))
		writer.close()
	'''

	'''
	def init_extra_ASP_strings(self):
		self.refined_planning_testing_rules_string = ('% Make sure the outcome of any concrete action is tested\n'
		                        'occurs(test(R, loc(R, C), true), I+1) :- occurs(move(R, C), I).\n'
		                        'occurs(test(R, in_hand(R, O), true), I+1) :- occurs(pickup(R, O), I).\n'
		                        'occurs(test(R, in_hand(R, O), false), I+1) :- occurs(put_down(R, O), I).\n'
		                        '-occurs(pickup(rob, OP), I) :- holds(loc(rob, C), I), not occurs(test(rob, loc(OP, C), true), I-1).\n'
		                        '-occurs(pickup(rob, OP), I) :- I = 0.')

		self.refined_planning_rules_string = ('%% Failure is not an option.\n'
		                            'success :- goal(I).\n'
		                            ':- not success.\n'
		                            '%% Plan Actions minimally\n'
		                            'occurs(A,I):+ not goal(I).\n'
		                            '%% Preventing preASP_refined_domain_no_planning\n'
		                            'something_happened(I) :- occurs(A, I).\n'
		                            ':- not goal(I), not something_happened(I).\n'
		                            ':- not something_happened(0).')
	'''

	def init_file_names(self):
		self.sparc_path = "$HOME/work/solverfiles/sparc.jar"
		pre_ASP_folder = 'pre_ASP_files/'
		ASP_folder = 'ASP_files/'

		self.domain_info_file = pre_ASP_folder + 'domain_info.txt'

		#self.file_name_preASP_abstract_domain = pre_pre_ASP_folder + 'pre_pre_ASP_abstract_domain.txt'
		#self.file_name_preASP_ToI_domain = pre_pre_ASP_folder + 'pre_pre_ASP_ToI_domain.txt'
		#self.file_name_pre_ASP_refined_domain = pre_pre_ASP_folder + 'pre_pre_ASP_refined_domain.txt'

		self.preASP_domain_file = pre_ASP_folder + 'preASP_Domain.txt'
		self.preASP_ToI_file = pre_ASP_folder + 'preASP_ToI.txt' # Used for astract planning and diagnosis with ToI
		#self.file_name_preASP_abstract_belief = pre_ASP_folder + 'preASP_abstract_belief.txt' # used for updating controller abstract belief
		#self.file_name_preASP_refined_planning = pre_ASP_folder + 'preASP_refined_planning.txt' # used for zoomed refined planning
		#self.file_name_preASP_inferring_indirect_observations = pre_ASP_folder + 'preASP_inferring_indirect_observations.txt' # used for inferring coarse observations
		#self.file_name_pre_ASP_refined_world = pre_ASP_folder + 'preASP_real_world.txt' # used for creating simulated world

		self.asp_ToI_planning_file = ASP_folder + 'ASP_ToI_Planning.sp'
		self.asp_ToI_diagnosing_file = ASP_folder + 'ASP_ToI_Diagnosis.sp'
		self.asp_ToI_defaults_file = ASP_folder + 'ASP_ToI_Defaults.sp'
		self.asp_World_file  = ASP_folder + 'ASP_World.sp'
		## used for paths and names of the ASP files created
		#self.asp_zoomed_domain_file = ASP_folder + 'Zoomed_Planning.sp'
		#self.asp_non_zoomed_domain_file = ASP_folder + 'Non_Zoomed_Planning.sp'
		#self.asp_abstract_belief_file = ASP_folder + 'Abstract_Belief.sp'
		#self.asp_inferring_indirect_observations_file = ASP_folder + 'Inferring_Indirect_Observations.sp'


	def init_files_markers(self):
		self.history_marker = '%% HISTORY GOES HERE'
		self.goal_marker = '%% GOAL GOES HERE'
		#self.refined_constants_marker = '%% CONSTANTS GO HERE'
		#self.sorts_marker = '%% SORTS GO HERE'
		#self.attributes_marker = '%% ATTRIBUTES GO HERE'
		#self.causal_law_marker = '%% CAUSAL LAWS GO HERE'
		#self.planning_marker = '%% PLANNING RULES GO HERE'
		#self.testing_marker = '%% TESTING RULES GO HERE'
		self.current_step_marker = '%% CURRENT STEP GOES HERE'
