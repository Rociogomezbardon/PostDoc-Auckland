''' The reasoning architecture of this controller cosists on two different levels of abstraction. One, at coarse-resolution level, the controller does the reasoning using the Theory of Intentions, and plans at abstract level. Then, for each coarse-resolution action the controller will create a plan at a fine-resolution level by using zooming (filtering out unnecesary information) into the refined representation of the domain, and create a refined plan to execute the abstract action.

The reasoning at coarse-resolution level has two phase. The first one is to diagnose the state of the coarse resolution domain  using its past coarse-resolution history and the coarse-resolution observations that the controller did during the execution of the last action. It creates, what we call, a consistent model of history. Once this is done, the controller will reason about its next inteded action at coarse-resolution level, based on the created model of history and its goal.

The reasoning at refined level has two phase. One is, given an abstract action that need executing, it will create a plan of refined actions that the robot can execute. If one of the refined actions cannot be executed, it will plan again at fine resolution level. In the second phase the execution of the abstract action has finished, it will reason about the fine-resolution observations that has been gathering during execution of refined actions, and it will infer the coarse-resolution observations, in order to be used by when reasoning at coarse-resolution level.
'''
from datetime import datetime
from datetime import timedelta
from sets import Set
from pprint import pprint
from collections import OrderedDict
import itertools
import subprocess
import re
import numpy as np
import global_variables
import multiprocessing
import inspect
import random
import copy
class ControllerToI():
	def __init__(self, domain_info, executer, refined_location, initial_conditions , goal):
		self.lines_to_write = [] #lines to write in the experimental_results.txt file
		self.goal = goal.replace(',holds', ', holds')
		print '\nGoal: ' + self.goal
		self.executer = executer
		self.domain_info = domain_info
		# variables relevant for the ASP_ToI planning and diagnosis
		self.number_toi_steps = 4 #initial total number of steps used for ASP planning
		self.number_activities = 1 #number of activitites the ASP needs
		self.goal_correction = 0 #number of times the goal has been assumed to be true but it was False
		self.current_diagnosis = '' #keeping the latest diagnosis
		self.input_for_planning = [] #past obs, attempts and diagnosis (as hpd statements)
		self.current_step = 1 #current step in controllerToI, (same as ASP_TOI_Planning)
		self.ASP_ToI_lines = self.get_ASP_ToI_lines()
		self.ASP_abstract_belief_lines =  self.get_ASP_abstract_belief_lines()
		self.setInitialBelief(self.cleanedUpHistory(initial_conditions))
		self.history_ToI_diagnosis = initial_conditions #past obs and attempts for ASP_ToI_Diagnosis
		self.refined_location = refined_location
		print ('ControllerToI ' + global_variables.controller_type + ' - initial coarse belief dictionary: ' + str(self.dic_belief))
		print ('ControllerToI - initial refined location: ' + str(self.refined_location))

	'''
	This method will run until the ASP_TOI_Planning returns 'finish' as next inteded action (and the goal is reached) or until the answer the asp is inconsistent because the goal is futile.
	'''
	def run(self, error, refinedPlanningTime, abstractPlanningTime, inferObsTime, diagnosingTime, execTime, numAbsPlans, numRefPlans, numAbsAct, numRefAct,completeRun):
		self.completeRun = completeRun
		self.abstractPlanningTime = abstractPlanningTime
		self.refinedPlanningTime = refinedPlanningTime
		self.inferObsTime = inferObsTime
		self.diagnosingTime = diagnosingTime
		self.execTime = execTime
		self.error = error
		self.believes_goal_holds = False
		self.history_ToI_diagnosis.append("hpd(select(my_goal), true,0).")

		self.executer.setTimer(self.execTime)
		## recoring purposes
		self.lines_to_write.append('\nRefined Location and Abstract Belief: ' + self.refined_location + ' ' + str(self.dic_belief))
		self.diagnose()
		finish = False # flag that breaks the loop that calls the ASP_ToI_Planning when finish == True
		while(finish == False and not self.error.is_set()):
			abstract_action = self.runToIPlanning(self.input_for_planning)
			if self.error.is_set(): break
			if(abstract_action == None):
				print ('ControllerToI ' + global_variables.controller_type + ' : \t Goal is futile ')
				self.history_ToI_diagnosis.append("Goal is futile")
				self.lines_to_write.append('\nGoal is futile ')
				finish = True
				break
			self.history_ToI_diagnosis.append('attempt('+abstract_action+','+str(self.current_step)+').')
			if(abstract_action == 'finish'):
				#check if the assuption that the goal has been reached is true.
				if(self.executer.isGoalReached(self.goal) == True):
					print('ControllerToI ' + global_variables.controller_type + ' : \t Belief: ' + str(self.dic_belief))
					print('ControllerToI ' + global_variables.controller_type + ' : \t Feedback from the workd: Belief is True')
					print('ControllerToI ' + global_variables.controller_type + ' : \t Finish')
					self.lines_to_write.append('\nBelief: ' + str(self.dic_belief))
					self.lines_to_write.append('\nFeedback from the workd: Belief is True')
					self.lines_to_write.append('\nFinish')
					self.completeRun.value = global_variables.character_code_complete_run
					finish = True
					break
				# if it is false, count the correction and diagnose again
				else:
					self.goal_correction += 1
					while(abstract_action == 'finish'):
						print('ControllerToI ' + global_variables.controller_type + ' : \t Feedback from the workd: Belief is False')
						self.history_ToI_diagnosis.append('obs(my_goal,false,'+str(self.current_step)+').')
						self.diagnose()
						if self.error.is_set(): break
						abstract_action = self.runToIPlanning(self.input_for_planning)
						if self.error.is_set(): break
			# if action is 'stop' it is because an unexpected action has happened and it needs to replan, so the number_activities should increase and be passed as part of the input to the ASP_ToI_Planning
			if(abstract_action[0:4] == 'stop'):
				self.number_activities += 1
				self.number_toi_steps += 1
			elif(abstract_action[0:5] == 'start'):
				numAbsPlans.value += 1
			else:
				print ('\nControllerToI ' + global_variables.controller_type + ' - next abstract action: ' + abstract_action)
				self.lines_to_write.append('\nnext abstract action: ' + abstract_action)
				need_refined_plan = True
				refined_plan_step = 0
				refined_history = self.create_refined_ASP(abstract_action) #holds all the history of the refined plan created wtih refined domain in form of 'hpd' and 'obs'
				ref_obs_goal = []
				initial_refined_location = self.refined_location
				while(need_refined_plan and not self.error.is_set()):
					refined_actions = [entry for entry in self.run_refined_ASP(self.sort_by_step(refined_history),abstract_action,refined_plan_step) if 'occurs' in entry]
					if self.error.is_set(): break
					numRefPlans.value += 1
					need_refined_plan = False
					refined_actions.sort(key=self.getStep)
					print ('ControllerToI ' + global_variables.controller_type + ' - refined plan: ' + str(refined_actions[refined_plan_step:]))
					self.lines_to_write.append('\nAbstract action: ' + str(abstract_action))
					self.lines_to_write.append('\nRefined plan: ' + str(refined_actions))
					last_action_needs_testing = False
					last_action = ''
					goal_direct_observations = ['holds('+v+','+str(refined_plan_step)+').' for v in self.getObservationsRelevantGoal()]
					execution_direct_observations = Set()

					for i in range(len(refined_actions)):
						refined_occurence = refined_actions[i]
						refined_action = refined_occurence[refined_occurence.find('(')+1 : refined_occurence.rfind(',')]
						occurrence_step = int(refined_occurence[refined_occurence.rfind(',')+1:refined_occurence.rfind(')')])
						if occurrence_step != refined_plan_step: continue
						print ('ControllerToI ' + global_variables.controller_type + ' - Refined action: ' + str(refined_action) + ' at refined step: ' + str(occurrence_step))
						if 'test' in refined_action:
							action_test_result, action_direct_observation = self.executer.test(refined_action)
							execution_direct_observations.add(self.domain_info.fluentToHoldsString(action_direct_observation,refined_plan_step))
							refined_history.add(self.domain_info.directObservationToObs(action_direct_observation, refined_plan_step))
							if last_action_needs_testing:
								if action_test_result==True : refined_history.add('hpd(' + last_action + ',' + str(refined_plan_step - 1) +').')
								last_action_needs_testing = False
								if 'put_down' in last_action:
									for o in self.test_nothing_in_hand(last_action):
										execution_direct_observations.add(self.domain_info.fluentToHoldsString(o,refined_plan_step))
										refined_history.add(self.domain_info.directObservationToObs(o, refined_plan_step))

							refined_history.add('hpd(' + refined_action + ',' + str(refined_plan_step) +').')

							refined_plan_step += 1
							if(action_test_result==True and 'loc(rob1' in refined_action):
								self.refined_location = action_direct_observation.split(',')[2][:-1]
								print ('ControllerToI ' + global_variables.controller_type + ' - Refined location: '+self.refined_location)
							goal_direct_observations = goal_direct_observations+['holds('+v+','+str(refined_plan_step)+').' for v in self.getObservationsRelevantGoal()]
							if(action_test_result == False):
								print ('ControllerToI ' + global_variables.controller_type + ' - Intended action did not happen - need another refined plan ')
								self.lines_to_write.append('\nIntended action did not happen - need another refined plan ')
								need_refined_plan = True
								break
						else:
							self.executer.executeAction(refined_action)
							last_action = refined_action
							last_action_needs_testing = True
							refined_plan_step += 1
						numRefAct.value += 1
				numAbsAct.value += 1
				all_direct_observations = Set(goal_direct_observations) | execution_direct_observations
				indirectObservations = self.infer_abstract_obs(all_direct_observations, refined_plan_step)

				if self.error.is_set(): break
				abstract_step_obs = Set([self.domain_info.indirectObservationToObs(entry[entry.find('(')+1:entry.rfind(',')],self.current_step+1) for entry in indirectObservations])

				print ('ControllerToI ' + global_variables.controller_type + ' - Abstract action ' +abstract_action+' has finished at step ' + str(self.current_step))
				print ('ControllerToI ' + global_variables.controller_type + ' - Abstract obs: ' + ': ' + str(abstract_step_obs))
				self.lines_to_write.append('\nAbstract action ' +abstract_action+' has finished at step ' + str(self.current_step))
				self.lines_to_write.append('\nAbstract obs: ' + ': ' + str(abstract_step_obs))
				self.update_abstract_belief(self.get_abstract_state_after_action(self.dic_belief, abstract_action, list(abstract_step_obs)))
				self.history_ToI_diagnosis = self.history_ToI_diagnosis + list(abstract_step_obs)
			self.current_step += 1
			self.diagnose()
		if(self.current_diagnosis != ''): self.history_ToI_diagnosis.append(self.current_diagnosis)
		self.recordFinalData('\n')

	def recordFinalData(self,message):
		print message
		results = open(global_variables.txt_results_file, 'a')
		for line in self.lines_to_write: results.write(line)
		results.write(message)
		results.close()

	'''
    This fuctions is used to ask the executer to observe if there is anything
	in_hand given the put_down action string as an input
	'''
 	def test_nothing_in_hand(self, put_down_action):
		observations = Set()
		put_down_object = put_down_action[put_down_action.find(',')+1:put_down_action.find(')')]
		myAbstractObject = self.domain_info.components_dic[put_down_object]
		myRefinedObjects = [k for k,v in self.domain_info.components_dic.items() if v == myAbstractObject]
		for ref_object in myRefinedObjects: observations.add(self.executer.test('test(rob1,in_hand(rob1,'+ref_object+'),true).')[1])
		return observations

	def getStep(self,myString):
		partOfString = myString[myString.rfind(',')+1:]
		myStep = map(int, re.findall('\d+', partOfString))[0]
		return int(myStep)

	def get_fluents_relevant_to_goal(self):
		return Set([self.domain_info.get_fluent(entry) for entry in self.goal.split(', ') ])

	def getObservationsRelevantGoal(self):
		observations = Set()
		relevantRefinedFluents = []
		refined_fluents_to_observe = Set()
		for myfluent in self.get_fluents_relevant_to_goal():
			thisObjectRefinedFluents = []
			objectsInAbstractFluent = [ob for ob in self.domain_info.refined_signature_dic['#coarse_object'] if ob in myfluent]
			abstractLocationIncluded = [loc for loc in self.domain_info.get_all_constant_subsorts('#coarse_place','refined') if loc in myfluent]
			for ob in objectsInAbstractFluent:
				refinedObjects = [refOb for refOb in self.domain_info.components_dic.keys() if self.domain_info.components_dic[refOb] == ob ]
				for refOb in refinedObjects:
					fluent = myfluent.replace(ob,refOb)
					for l in abstractLocationIncluded: fluent = fluent.replace(l,self.refined_location)
					refined_fluents_to_observe.add(fluent)


		for refFluent in refined_fluents_to_observe:
			result, observation = self.executer.test('test(rob1,' + refFluent +',true)')
			observations.add(observation)
		return list(observations)

	'''
	This function runs the refined asp held in the file asp_zoomed_domain_file or asp_non_zoomed_domain_file depending on whether the controller is running in
	zoomed or non-zoomed mode. It has the refeind history, abstract action and refined plan step as input, and it returns the first answer of the answer set run.
	'''
	def run_refined_ASP(self,refined_history,abstract_action,refined_plan_step):
		numStepsPlanning = max(5,refined_plan_step+1) #starting one step ahead of the plan we have so far, if it has already startes
		if 'pickup' in abstract_action: numStepsPlanning = max(5,refined_plan_step+4) #when searching for an object, each time that the pick up fails, the agent needs at least 4 more actions to plan to move to the next cell, test its movement, test the loation of the object and pickup.
		for i,l in enumerate(self.refined_planning_relevant_lines):
			if self.domain_info.history_marker in l: self.refined_planning_relevant_lines[i] = self.refined_planning_relevant_lines[i] + '\n' + '\n'.join(refined_history)


		self.refined_planning_relevant_lines[0] = '#const numSteps = ' + str(numStepsPlanning) +'.'
		asp = '\n'.join(self.refined_planning_relevant_lines)
		if global_variables.controller_type == 'zooming': myFile = self.domain_info.asp_zoomed_domain_file
		else: myFile = self.domain_info.asp_non_zoomed_domain_file

		f1 = open(myFile, 'w')
		f1.write(asp)
		f1.close()
		answer_set = ''
		print myFile + ' with number of steps: ' + str(numStepsPlanning)
		startTime = datetime.now()
		try:
			answer_set = subprocess.check_output('java -jar '+self.domain_info.sparc_path + ' ' + myFile +' -A',shell=True)
		except subprocess.CalledProcessError, e:
			self.refinedPlanningTime.value += (datetime.now() - startTime).total_seconds()
			lineno = self.lineno()
			self.completeRun.value = global_variables.character_code_too_many_answers
			self.recordFinalData('\nError running '+myFile+'; caught at line '+str(lineno))
			self.recordFinalData(e.output)
			#pprint(asp)
			self.set_error()
			return None
		self.refinedPlanningTime.value += (datetime.now() - startTime).total_seconds()
		if answer_set == '':
			lineno = self.lineno()
			self.completeRun.value = global_variables.character_code_too_many_answers
			self.recordFinalData('\nToo many answers on ASP '+myFile+'; caught at line '+str(lineno))
			#pprint(asp)
			self.set_error()
			return None
		self.lines_to_write.append('\nTime taken to create refined plan for abstract action: '+abstract_action+', ' + str(datetime.now() - startTime))
		chosenAnswer = ''
		#if refined_plan_step == 0:
		#	numStepsPlanning = 5

		while answer_set == '\n' and numStepsPlanning < self.domain_info.max_number_steps_refined_planning:
			numStepsPlanning +=1
			reader = open(myFile, 'r')
			my_text = reader.read()
			reader.close()
			asp = my_text.split('\n')
			asp[0] = '#const numSteps = '+ str(numStepsPlanning) +'.'
			writer = open(myFile, 'w')
			writer.write('\n'.join(asp))
			writer.close()
			answer_set = ''
			print myFile + ' with number of steps: ' + str(numStepsPlanning)
			startTime = datetime.now()
			answer_set = subprocess.check_output('java -jar '+self.domain_info.sparc_path + ' ' + myFile +' -A',shell=True)
			self.refinedPlanningTime.value += (datetime.now() - startTime).total_seconds()
			self.lines_to_write.append('\nTime taken to create refined plan with a max of '+ str(numStepsPlanning)+' steps: ' + str(datetime.now() - startTime))
			if answer_set == '':
				lineno = self.lineno()
				self.completeRun.value = global_variables.character_code_too_many_answers
				self.recordFinalData('\nToo many answers on ASP '+myFile+'; caught at line '+str(lineno))
				#pprint(asp)
				self.set_error()
				return None
		if answer_set == '\n' and numStepsPlanning >= self.domain_info.max_number_steps_refined_planning:
			lineno = self.lineno()
			self.completeRun.value = global_variables.character_code_inconsistency
			self.recordFinalData('\nInconsistency on ASP '+myFile+'; caught at line '+str(lineno))
			#pprint(asp)
			self.set_error()
			return None
		answer_set_split = answer_set.rstrip().split('\n\n')
		if 'put_down' in abstract_action:
			for answer in answer_set_split:
				if 'put_down' in answer: return answer.strip('{').strip('}').split(', ')
		return answer_set_split[0].strip('{').strip('}').split(', ')

	def cleanedUpHistory(self,this_list):
		return [a for a in this_list if 'select' not in a and 'start' not in a and 'stop' not in a]

	def runToIPlanning(self,input):
		startTime = datetime.now() # record the time taken to plan the abstract plan
		abstract_action = None
		new_ASP_ToI_lines = self.ASP_ToI_lines[:]
		new_ASP_ToI_lines[new_ASP_ToI_lines.index(self.domain_info.history_marker)]= '\n'.join(input)
		new_ASP_ToI_lines[self.ASP_ToI_lines.index(self.domain_info.current_step_marker)] = 'current_step('+str(self.current_step)+').'
		new_ASP_ToI_lines[0] = "#const numSteps = "+str(self.number_toi_steps+1)+". % maximum number of steps."
		new_ASP_ToI_lines[1] = "#const max_len = "+str(self.number_toi_steps)+". % maximum activity_length of an activity."
		new_ASP_ToI_lines[2] = "#const max_name = " + str(self.number_activities) + "."
		asp = '\n'.join(new_ASP_ToI_lines)
		myFile = self.domain_info.asp_ToI_planning_file
		f1 = open(myFile, 'w')
		f1.write(asp)
		f1.close()
		print myFile + ' \t\t Finding next intended action'
		answer_set = subprocess.check_output('java -jar '+self.domain_info.sparc_path + ' ' + myFile +' -A ',shell=True)
		self.abstractPlanningTime.value += (datetime.now() - startTime).total_seconds()
		counter = 0
		counter += 1
		this_abstract_planning_time = datetime.now() - startTime
		if answer_set == '':
			lineno = self.lineno()
			self.completeRun.value = global_variables.character_code_too_many_answers
			self.recordFinalData('\nToo many answers on ASP '+myFile+'; caught at line '+str(lineno))
			#pprint(asp)
			self.set_error()
			return None
		max_step = int(self.current_step + self.domain_info.max_number_steps_ToI_planning+2)
		step_num = int(self.number_toi_steps)
		if (step_num < max_step): max_reached = True
		else: max_reached = False
		while( not ("intended_action" in answer_set) and not ("selected_goal_holds" in answer_set) and max_reached):
			new_ASP_ToI_lines[0] = "#const numSteps = "+str(self.number_toi_steps+1)+". % maximum number of steps."
			new_ASP_ToI_lines[1] = "#const max_len = "+str(self.number_toi_steps)+". % maximum activity_length of an activity."
			asp = '\n'.join(new_ASP_ToI_lines)
			f1 = open(myFile, 'w')
			f1.write(asp)
			f1.close()
			print myFile
			startTime = datetime.now()
			answer_set = subprocess.check_output('java -jar '+self.domain_info.sparc_path + ' ' + myFile +' -A ',shell=True)
			self.abstractPlanningTime.value += (datetime.now() - startTime).total_seconds()
			this_abstract_planning_time += datetime.now() - startTime
			counter += 1
			if answer_set == '':
				lineno = self.lineno()
				self.completeRun.value = global_variables.character_code_too_many_answers
				self.recordFinalData('\nToo many answers on ASP '+myFile+'; caught at line '+str(lineno))
				#pprint(asp)
				self.set_error()
				return None
			self.number_toi_steps +=1
			step_num = int(self.number_toi_steps)
			if (step_num < max_step): max_reached = True
			else: max_reached = False
		possibleAnswers = answer_set.rstrip().split('\n\n')
		chosenAnswer = possibleAnswers[0]
		split_answer = chosenAnswer.strip('}').strip('{').split(', ')
		self.history_ToI_diagnosis = []
		self.believes_goal_holds = False
		for line in split_answer:
			if("intended_action" in line):
				abstract_action = line[16:line.rfind(',')]
			elif("selected_goal_holds" in line):
				self.believes_goal_holds = True
			else:
				self.history_ToI_diagnosis.append(line + '.')
		if(abstract_action[0:5] == 'start'):
			myPlan = [entry for entry in split_answer if 'comp' in entry]
			self.lines_to_write.append('\nAbstract action plan: ' + str(myPlan))
		self.lines_to_write.append('\nTime taken to plan abstract action plan: ' + str(this_abstract_planning_time))
		return abstract_action

	def diagnose(self):
		startTime = datetime.now()
		self.input_for_planning = []
		possibleDiagnosis = []
		input = list(self.history_ToI_diagnosis)
		input.append("explaining("+str(self.current_step)+").")
		new_ASP_ToI_lines = self.ASP_ToI_lines[:]
		new_ASP_ToI_lines[new_ASP_ToI_lines.index(self.domain_info.history_marker)] = '\n'.join(input)
		new_ASP_ToI_lines[self.ASP_ToI_lines.index(self.domain_info.current_step_marker)] = 'current_step('+str(self.current_step)+').'
		new_ASP_ToI_lines[0] = "#const numSteps = "+str(self.number_toi_steps+1)+". % maximum number of steps."
		new_ASP_ToI_lines[1] = "#const max_len = "+str(self.number_toi_steps)+". % maximum activity_length of an activity."
		new_ASP_ToI_lines[2] = "#const max_name = " + str(self.number_activities) + "."
		asp = '\n'.join(new_ASP_ToI_lines)
		myFile = self.domain_info.asp_ToI_diagnosing_file
		f1 = open(myFile, 'w')
		f1.write(asp)
		f1.close()
		print myFile
		startTime = datetime.now()
		answer_set = subprocess.check_output('java -jar '+self.domain_info.sparc_path + ' ' + myFile +' -A ',shell=True)
		self.diagnosingTime.value += (datetime.now() - startTime).total_seconds()
		self.lines_to_write.append('\nTime taken to diagnose: ' + str(datetime.now() - startTime))
		if answer_set == '':
			lineno = self.lineno()
			self.completeRun.value = global_variables.character_code_too_many_answers
			self.recordFinalData('\nToo many answers on ASP '+myFile+'; caught at line '+str(lineno))
			#pprint(asp)
			self.set_error()
			return
		answers = answer_set.rstrip().split('\n\n')
		if self.current_diagnosis in answer_set:
			for a in answers:
				if(self.current_diagnosis in a): chosenAnswer = a
		else:
			chosenAnswer = answers[0]

		split_diagnosis = chosenAnswer.strip('}').strip('{').split(', ')
		for line in split_diagnosis:
			if("number_unobserved" in line):
				newLine =line.replace("number_unobserved","explanation")
				self.input_for_planning.append(newLine + '.')
			elif("unobserved" in line):
				newLine = line.replace("unobserved", "occurs") + '.'
				self.input_for_planning.append(newLine)
				if(self.current_diagnosis != line):
					self.update_abstract_belief(self.get_abstract_state_after_action(self.dic_belief,line[line.find('(')+1:line.rfind(',')],[]))
					self.current_diagnosis = line
					print ('ControllerToI - new diagnosis: ' + self.current_diagnosis)
			elif("selected_goal_holds" in line): pass
			elif(line == ""): pass
			else:
				self.input_for_planning.append(line + '.')
		self.lines_to_write.append('\nDiagnosis: ' + str(self.current_diagnosis))


	def get_ASP_ToI_lines(self):
		reader = open(self.domain_info.file_name_preASP_ToI_planning, 'r')
		ASP_ToI_lines = reader.read().split('\n')
		reader.close()
		ASP_ToI_lines[ASP_ToI_lines.index(self.domain_info.goal_marker)] = "holds(my_goal,I) :- "+ self.goal
		return ASP_ToI_lines

	def get_ASP_abstract_belief_lines(self):
		reader = open(self.domain_info.file_name_preASP_abstract_belief, 'r')
		preASP_domain = reader.read()
		reader.close()
		return preASP_domain.split('\n')

	# This returns what the abstract state would be, considering
	# the initial_state, the action, and a list of observations given as parameters.
	# It is used for createing refined plans, and also to update the belief
	# of the controller when an action has happend.
	def get_abstract_state_after_action(self, initial_state, action, obsList):
		if('start' in action or 'stop' in action): return
		possible_last_action = 'hpd(' +action+', 0).'
		obsList = [a[:a.rfind(',')] + ',1).' for a in obsList]
		input = list(self.domain_info.dic_abstractStateToAbstractHoldsSet(initial_state,0)) + [possible_last_action] + obsList
		asp_belief_lines = self.ASP_abstract_belief_lines[:]
		asp_belief_lines[asp_belief_lines.index(self.domain_info.history_marker)] = '\n'.join(input)
		asp_belief_lines[0] = "#const numSteps = 1."
		asp = '\n'.join(asp_belief_lines)
		myFile = self.domain_info.asp_abstract_belief_file
		f1 = open(myFile, 'w')
		f1.write(asp)
		f1.close()
		print myFile
		startTime = datetime.now()
		answer_set = subprocess.check_output('java -jar '+ self.domain_info.sparc_path + ' ' + myFile +' -A',shell=True)
		self.abstractPlanningTime.value += (datetime.now() - startTime).total_seconds()
		if answer_set == '\n':
			lineno = self.lineno()
			self.completeRun.value = global_variables.character_code_inconsistency
			self.recordFinalData('\nInconsistency on ASP '+myFile+'; caught at line '+str(lineno))
			#pprint(asp)
			self.set_error()
			return None
		answer_split = ((answer_set.rstrip().split('\n\n'))[0]).strip('{}\n').split(', ')
		return self.domain_info.dic_answerToState(answer_split)

	def update_abstract_belief(self,new_state):
		if len(new_state) > 0: self.dic_belief = new_state

	# it sets the initial coarse-resolution belief of the controller
	def setInitialBelief(self,input):
		asp_belief_lines = self.ASP_abstract_belief_lines[:]
		asp_belief_lines[asp_belief_lines.index(self.domain_info.history_marker)] = '\n'.join(input)
		asp_belief_lines[0] = "#const numSteps = "+ str(self.current_step) + "."
		asp = '\n'.join(asp_belief_lines)
		myFile = self.domain_info.asp_abstract_belief_file
		f1 = open(myFile, 'w')
		f1.write(asp)
		f1.close()
		print ('\nControllerToI ' + global_variables.controller_type + ' : Setting initial belief')
		print myFile
		startTime = datetime.now()
		answer_set = subprocess.check_output('java -jar '+ self.domain_info.sparc_path + ' ' + myFile +' -A',shell=True)
		if answer_set == '' or answer_set == '\n':
			lineno = self.lineno()
			if answer_set == '':
				self.completeRun.value = global_variables.character_code_too_many_answers
				self.recordFinalData('\nToo many answers on ASP '+myFile+'; caught at line '+str(lineno))
			elif answer_set == '\n':
				self.completeRun.value = global_variables.character_code_inconsistency
				self.recordFinalData('\nInconsistency on ASP '+myFile+'; caught at line '+str(lineno))
			#pprint(asp)
			self.set_error()
			return
		answer_split = ((answer_set.rstrip().split('\n\n'))[0]).strip('{}\n').split(', ')
		self.dic_belief = self.domain_info.dic_answerToState(answer_split)


	#The lines for refined zooming follow the steps explained in paper REBA

	def prepare_lines_refined_zoom(self, action):
		initial_state = self.dic_belief
		initial_conditions_list = self.domain_info.dic_abstractStateToAbstractHoldsSet(initial_state,0)
		final_state = self.get_abstract_state_after_action(initial_state,action,[])
		final_conditions_list = self.domain_info.dic_abstractStateToAbstractHoldsSet(final_state,'I')
		timeless_initial_conditions_list = [condition[:condition.find(')')] for condition in initial_conditions_list]
		timeless_final_conditions_list = [condition[:condition.find(')')] for condition in final_conditions_list]
		conditions_for_action = Set(timeless_initial_conditions_list) ^ Set(timeless_final_conditions_list)

		#creating the relObjConst Set. These three constants will allways be relevant to the zoomed domains.
		rel_constants = Set({'true','false','undet'})
		#addding the constants used as parameter values for the action or that appear in conditions that change with action
		for o in self.domain_info.refined_constants:
			if o in action: rel_constants.add(o)
			for c in conditions_for_action:
				if o in c: rel_constants.add(o)


 		# finding all constants that  appear in the condtions of grounded executablitity conditions relevant to the grounded action
		action_parameter_values = action[action.find('(')+1:action.find(')')].split(',')
		# find executability conditions and parameteres
		param_and_exec_conditions_set = self.domain_info.actions_param_and_exec_conditions_dic[action[:action.find('(')]]
		parameters = param_and_exec_conditions_set[0]
		exec_conditions = param_and_exec_conditions_set[1]
		partially_grounded_exec_conditions = exec_conditions.copy()

		for parameter,value in zip(parameters, action_parameter_values):
			partially_grounded_exec_conditions = Set(self.domain_info.replace_parameter_in_conditions_list(parameter,value,list(partially_grounded_exec_conditions)))

		# add all constants relevant if they appear in the conditions of grounded executablitity conditions relevant to the action
		fully_grounded_exec_conditions = self.domain_info.all_possible_groundings(partially_grounded_exec_conditions,'abstract')
		fully_grounded_exec_conditions_step_0 = [c+',0).' for c in fully_grounded_exec_conditions]
		## make sure initial conditions are in abstract format before comparing them with the grounded fluents.
		fully_grounded_exec_conditions_in_initial_conditions = Set(initial_conditions_list).intersection(fully_grounded_exec_conditions_step_0)
		for condition in fully_grounded_exec_conditions_in_initial_conditions:
			rel_constants.update(Set(self.domain_info.get_parameters(self.domain_info.get_fluent(condition))))


		#add refine the relevant abstract objects and add them to the observed_refined_constants:
		observed_refined_constants = Set()
		for abstract_object_constant in rel_constants.copy():
			for refined_object in self.domain_info.components_dic.keys():
				if self.domain_info.components_dic[refined_object] == abstract_object_constant: observed_refined_constants.add(refined_object)
		rel_constants.update(observed_refined_constants)


		#get all the relevant sorts following the initial sorts hierarchy
		self.action_refined_signature_dic = self.domain_info.infer_relevant_refined_signature_dic(rel_constants)
		irrelevant_sorts = Set(self.domain_info.refined_signature_dic.keys()) - Set(self.action_refined_signature_dic.keys())
		irrelevant_constants =  self.domain_info.refined_constants - rel_constants
		irrelevant_objects = irrelevant_constants.union(irrelevant_sorts)


		#starting with all the initial conditions as relevant, we will remove those conditions that contains irrelevant objects (constants, fluents, or actions)
		relevant_initial_conditions = Set(initial_conditions_list)
		for condition in initial_conditions_list:
			for entry in irrelevant_objects:
				if entry in re.findall(self.domain_info.reg_exp_sorts,condition): relevant_initial_conditions.discard(condition)

		# format the conditions so that they are in coarse form
		# also add refined loc and assumed ref in hand if their course level counterparts are part of the relevant initial conditions
		new_relevant_initial_conditions = Set()
		for c in relevant_initial_conditions:
			c = c.replace('holds(','holds(coarse_')
			new_relevant_initial_conditions.add(c)
			if  c[:c.find(',')] == 'holds(coarse_in_hand(rob1':
				abstract_object_holding =  self.dic_belief['in_hand(rob1']
				all_refined_parts_of_abstract_object_holding = [k for k,v in self.domain_info.components_dic.items() if v == abstract_object_holding]
				chosen_ref_part = random.choice(all_refined_parts_of_abstract_object_holding)
				new_relevant_initial_conditions.add('holds(in_hand(rob1,'+chosen_ref_part+'),0).')
			if c[:c.find(',')] == 'holds(coarse_loc(rob1':
				new_relevant_initial_conditions.add('holds(loc(rob1,' + self.refined_location+'),0).')
		relevant_initial_conditions = new_relevant_initial_conditions

		relevant_final_conditions = Set(final_conditions_list)
		for condition in final_conditions_list:
			for entry in irrelevant_objects:
				if entry in re.findall(self.domain_info.reg_exp_sorts,condition): relevant_final_conditions.discard(condition)

		#remove last dot of the final conditions to get them ready for the goal string
		relevant_final_conditions_list = [v.replace('holds(','holds(coarse_').strip('.') for v in list(relevant_final_conditions)]
		goal = 'goal(I) :- ' + ', '.join(relevant_final_conditions_list) + '.'


		signature_info_lines = '\n'.join(self.domain_info.create_signature_lines(self.action_refined_signature_dic))

		# read the preASP text and discard irrelevant lines
		original_asp_reader = open(self.domain_info.file_name_preASP_refined_planning, 'r')
		pre_ASP_refined_planning_lines = (original_asp_reader.read()).split('\n')
		original_asp_reader.close()

		# find indexes of irrelevant lines
		irrelevant_indexes = Set()
		for i,line in enumerate(pre_ASP_refined_planning_lines):
			for object in irrelevant_objects:
				if object in re.findall(self.domain_info.reg_exp_sorts,line): irrelevant_indexes.add(i)

		# copy only relevant lines
		all_indexes = Set(range(len(pre_ASP_refined_planning_lines)))
		relevant_lines = [pre_ASP_refined_planning_lines[i] for i in sorted(all_indexes ^ irrelevant_indexes)]

		for i,l in enumerate(relevant_lines):
			if self.domain_info.sorts_marker in l: relevant_lines[i] = relevant_lines[i] + '\n' +  '\n'.join(self.domain_info.create_signature_lines(self.action_refined_signature_dic))
			if self.domain_info.history_marker in l: relevant_lines[i] = relevant_lines[i] + '\n' + '\n'.join(relevant_initial_conditions)
			if self.domain_info.goal_marker in l: relevant_lines[i] = relevant_lines[i] + '\n' + goal

		self.refined_planning_relevant_lines = relevant_lines

		return relevant_initial_conditions

	# This method prepares an ASP to infer the coarse resolution indirect observations
	# from the refined level  direct-observations. The ASP only includes in the signature
	# all those objects that appear in the direct_observations, and its counterparts, and # the refined parts of the coutnerparts.
	# The does not include any actions, executability conditions, causal laws, or state
	# constrains.
	# It only includes rules related to attributes and fine-resolution counterparts,
	# CWA  Defined Fluents, Inertia Axioms and bridge Axioms for inferrnig observations.
	def infer_abstract_obs(self, direct_observations,steps):
		inferring_complete_singature_dic = copy.deepcopy(self.domain_info.refined_signature_dic)
		#removing actions of my new signature dic
		for a in self.domain_info.get_all_function_subsorts('#action','refined'): inferring_complete_singature_dic.pop(a, None)

		observed_refined_constants = Set([c for c in self.domain_info.get_all_constant_subsorts('#refined_component','refined') if c in re.findall(r"[\w']+", ','.join(direct_observations))])
		relevant_abstract_constants = Set([self.domain_info.components_dic[r] for r in observed_refined_constants])
		relevant_refined_constants = Set([r for r in self.domain_info.components_dic.keys() if self.domain_info.components_dic[r] in relevant_abstract_constants])
		all_relevant_constants =self.domain_info.get_all_constant_subsorts('#robot','refined')|Set({'true','false','undet'})|relevant_abstract_constants|relevant_refined_constants
		#print re.findall(r"[\w']+", ','.join(direct_observations))
		new_signature_dic = self.domain_info.infer_relevant_refined_signature_dic_form_given_hierarchy_dic(all_relevant_constants,inferring_complete_singature_dic)
		new_signature_string = '\n'.join(self.domain_info.create_signature_lines(new_signature_dic))
		my_components_lines = ['comp('+r+','+self.domain_info.components_dic[r]+').' for r in relevant_refined_constants]
		reader = open(self.domain_info.file_name_preASP_inferring_obs, 'r')
		relevant_lines = (reader.read()).split('\n')
		reader.close()
		relevant_lines[0] = '#const numSteps = ' + str(steps) +'.'
		relevant_lines[relevant_lines.index(self.domain_info.sorts_marker)] = new_signature_string
		relevant_lines[relevant_lines.index(self.domain_info.attributes_marker)] = '\n'.join(my_components_lines)
		relevant_lines[relevant_lines.index(self.domain_info.history_marker)] = '\n'.join(direct_observations)
		myFile =self.domain_info.asp_inferring_indirect_obs_file

		f1 = open(myFile, 'w')
		f1.write('\n'.join(relevant_lines))
		f1.close()
		print ('\nControllerToI ' + global_variables.controller_type + ' : Inferring indirect coarse obs from refined direct observations ')
		print myFile
		startTime = datetime.now()
		answer_set = subprocess.check_output('java -jar '+self.domain_info.sparc_path + ' ' + myFile +' -A ', shell=True)
		self.inferObsTime.value += (datetime.now() - startTime).total_seconds()
		if answer_set == '' or answer_set =='\n':
			lineno = self.lineno()
			if answer_set == '':
				self.completeRun.value = global_variables.character_code_too_many_answers
				self.recordFinalData('\nToo many answers on ASP '+myFile+'; caught at line '+str(lineno))
			elif answer_set == '\n':
				self.completeRun.value = global_variables.character_code_inconsistency
				self.recordFinalData('\nInconsinstancy on ASP '+myFile+'; caught at line '+str(lineno))
			asp = relevant_lines
			#pprint(asp)
			self.set_error()
			return None
		answer_split = ((answer_set.rstrip().split('\n\n'))[0]).strip('{').strip('}').split(', ')
		print '\nInferred Abstract Obs: ' + str(answer_split)
		if answer_split == ['']: return Set()
		return Set(answer_split)


	# This function is used to prepare the lines for an ASP file of the refined
	# domain, without zooming.
	def prepare_lines_refined_no_zoom(self,action):
		final_state = self.get_abstract_state_after_action(self.dic_belief,action,[])
		final_conditions_list = [c.strip('.') for c in list(self.domain_info.dic_abstractStateToCoarseHoldsSet(final_state,'I'))]
		initial_conditions = self.domain_info.dic_abstractStateToCoarseHoldsSet(self.dic_belief, 0)
		initial_conditions.add('holds(loc(rob1,'+self.refined_location+'),0).')
		reader = open(self.domain_info.file_name_preASP_refined_planning, 'r')
		relevant_lines = reader.read().split('\n')
		goal = 'goal(I) :- ' + (',').join(final_conditions_list) + '.'
		for i,l in enumerate(relevant_lines):
			if self.domain_info.sorts_marker in l: relevant_lines[i] = relevant_lines[i] + '\n' +   '\n'.join(self.domain_info.refined_sorts_lines)
			if self.domain_info.goal_marker in l: relevant_lines[i] = relevant_lines[i] + '\n' + goal
		self.refined_planning_relevant_lines = relevant_lines
		return initial_conditions

	# This function uses the preASP_refined_Domain.txt file and SPARC to
	# create a refined ASP (zoomed or non-zoomed) that will create a refined action plan.
	# This function returns the initial state strings that should be included in the refined history.
	def create_refined_ASP(self, action):
		refined_initial_state = Set()
		if(global_variables.controller_type == 'zooming'):
			refined_initial_state = self.prepare_lines_refined_zoom(action)
		elif(global_variables.controller_type == 'non_zooming'):
			refined_initial_state = self.prepare_lines_refined_no_zoom(action)
		return refined_initial_state

	#this function gets a sequence of entries from the history and sorts them by step.
	def sort_by_step(self,sequence):
		historyInfoSplit = [entry.rstrip(').').split(',') for entry in sequence]
		historyInfoSplit.sort(key=lambda x:x[0],reverse=True)
		historyInfoSplit.sort(key=lambda x:int(x[-1]))
		return [','.join(entry)+').' for entry in historyInfoSplit]

	def lineno(self):
		return inspect.currentframe().f_back.f_lineno

	def set_error(self):
		self.error.set()
