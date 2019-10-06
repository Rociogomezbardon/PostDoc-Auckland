from sets import Set
#import global_variables
from pprint import pprint
from collections import OrderedDict
import re
import random
import itertools
class DomainInfoFormatting():
	def __init__(self):

		self.init_file_names()
		self.init_files_markers()

		self.abstract_signature_dic = OrderedDict()
		self.abstract_signature_lines = []
		self.abstract_attributes_lines = []
		is_abstract_signature_line = False
		is_abstract_attributes_line = False
		with open(self.domain_info_file) as f:
			for line in f:
				line = line.strip()
				if line == '%% Abstraction_1 Sorts':
					is_abstract_signature_line = True
					continue
				elif line == '%% End of Abstraction_1 Sorts':
					is_abstract_signature_line = False
					continue
				elif line == '%% Abstraction_1 Attributes':
					is_abstract_attributes_line = True
					continue
				elif line == '%% End of Abstraction_1 Attributes':
					is_abstract_attributes_line = False
					continue
				elif 'max_number_steps_ToI_planning' in line:
					self.max_number_steps_ToI_planning = int(re.search(r'\d+', line).group()) #get the integer in the line

				if is_abstract_signature_line:
					self.abstract_signature_lines.append(line)
					if '#' not in line: continue
					line_split = line.replace(' ','').strip('.').split('=')
					sort_name = line_split[0]
					sort_composition_string = line_split[1]
					sort_composition_list = sort_composition_string.split('+')
					if '{' in sort_composition_list[0] or sort_composition_list[0] in self.abstract_signature_dic.keys():
						sort_composition_set = Set([v for v in sort_composition_list if v in self.abstract_signature_dic.keys()])
						for v in sort_composition_list:
							 if '{' in v: sort_composition_set.update(Set(v.strip('{}').split(',')))
						self.abstract_signature_dic[sort_name] = sort_composition_set
					elif '(' in sort_composition_list[0] or sort_composition_list[0] in self.abstract_signature_dic.keys():
						sort_composition_set = Set([v for v in sort_composition_list if v in self.abstract_signature_dic.keys()])
						for v in sort_composition_list:
							if '(' in v:
								v = v.strip(')').split('(')
								self.abstract_signature_dic[v[0]] = v[1].split(',')
								sort_composition_set.add(v[0])
						self.abstract_signature_dic[sort_name] = sort_composition_set

				if is_abstract_attributes_line: self.abstract_attributes_lines.append(line)

		self.abstract_constants = Set()
		for values in self.abstract_signature_dic.values(): self.abstract_constants.update(Set([v for v in values if v not in self.abstract_signature_dic.keys()]))
		self.functions = Set([v for v in self.abstract_signature_dic.keys() if '#' not in v  and v not in self.abstract_constants])

	def get_all_constant_subsorts(self,sort):
		if sort in self.abstract_constants: return sort
		my_subsorts = self.abstract_signature_dic[sort]
		my_constant_subsorts = my_subsorts & self.abstract_constants
		not_constant_sorts = my_subsorts - my_constant_subsorts
		for s in not_constant_sorts: my_constant_subsorts.update(self.get_all_constant_subsorts(s))
		return my_constant_subsorts

	def get_all_function_subsorts(self,sort):
		if sort in self.functions: return sort
		my_subsorts = self.abstract_signature_dic[sort]
		my_function_subsorts = my_subsorts & self.functions
		not_function_sorts = my_subsorts - my_function_subsorts
		for s in not_function_sorts: my_function_subsorts.update(self.get_all_function_subsorts(s))
		return my_function_subsorts

	'''
	#TODO needs testing
	this function gets a dictionary that represents a state, and returns a list of obs strings that
	hold all the information about this state.
	'''
	def dic_state_to_holds_list(self,dic_state,step):
		robot_name = list(self.get_all_constant_subsorts('#robot'))[0]
		obsList = ['holds('+','.join([v for v in [a,b] if v])+'),'+str(step)+').' for a,b in dic_state.items()]
		if [v for v in dic_state.keys() if 'in_hand' in v] == []:
			obsList = obsList + ['-holds(in_hand('+robot_name+','+ object +'),'+ str(step) +').' for object in self.get_all_constant_subsorts('#object')]
		if 'locked(library' not in dic_state.keys(): obsList.append('-holds(locked(library),' +str(step) + ').')
		return obsList



	def dic_state_to_obs_list(self,dic_state,step):
		return self.holds_to_obs_list(self.dic_state_to_holds_list(dic_state,step))


	def holds_to_obs_list(self,holds_strings):
		initial_obs_strings = [v.replace('holds','obs').replace('),','),true,') if '-' not in v else v.replace('-holds','obs').replace('),','),false,')  for v in holds_strings]
		return initial_obs_strings


	# it returns the list of paramterers in the fluent that has been given as input.
	def get_parameters(self,fluent):
		return fluent[fluent.find('(')+1:fluent.find(')')].split(',')


	# it returns the fluent that is part of the 'holds' string that has been given as input
	# for example get_fluent('holds(loc(rob1,kitchen),0)' will return 'loc(rob1,kitchen)')
	def get_fluent(set,holds_string):
		return holds_string[holds_string.find('(')+1:holds_string.find(')')+1]

	def dic_answerToState(self,answer):
		dic_coarse_state = {}
		answer_split =  answer.rstrip().strip('{').strip('}').split(', ')
		for holds_string in answer_split:
			if '-' in holds_string: continue
			fluent = holds_string[holds_string.find('(')+1:holds_string.rfind(',')]
			fluent_split = (fluent[:-1]).split(',')
			dic_coarse_state[fluent_split[0].encode('ascii', 'ignore')] = fluent_split[1].encode('ascii', 'ignore')
		return dic_coarse_state

	def init_file_names(self):
		self.sparc_file = "$HOME/work/solverfiles/sparc_2.jar"
		pre_ASP_folder = 'pre_ASP_files/'
		ASP_folder = 'ASP_files/'
		self.domain_info_file = pre_ASP_folder + 'domain_info.txt'
		self.preASP_domain_file = pre_ASP_folder + 'preASP_Domain.txt'
		self.preASP_toi_file = pre_ASP_folder + 'preASP_ToI.txt' # Used for astract planning and diagnosis with ToI
		self.asp_ToI_planning_file = ASP_folder + 'ASP_ToI_Planning.sp'
		self.asp_ToI_diagnosing_file = ASP_folder + 'ASP_ToI_Diagnosis.sp'
		self.asp_ToI_defaults_file = ASP_folder + 'ASP_ToI_Defaults.sp'
		self.asp_World_file  = ASP_folder + 'ASP_World.sp'
		## used for paths and names of the ASP files created


	def init_files_markers(self):
		self.history_marker = '%% HISTORY GOES HERE'
		self.goal_marker = '%% GOAL GOES HERE'
		self.current_step_marker = '%% CURRENT STEP GOES HERE'
