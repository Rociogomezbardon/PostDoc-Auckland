import os
import subprocess
import re
from datetime import datetime
class Controller_ToA(object):

	def __init__(self,sparcPath):
		self.toa_pre_asp_file = 'preASP_ToA.txt'
		self.toa_asp_file = 'ASP_ToA.sp'
		self.new_activity_asp_file = 'New_Activity_ToA.sp'
		self.activities_file = 'activities.txt'
		self.traditional_pre_asp_file = 'preASP_Traditional.txt'

		self.sparcPath = sparcPath
		self.toa_pre_asp_split = []
		self.traditional_pre_asp_split = []
		self.activities_list = []
		self.__updateActivitiesFile()
		self.__read_toA_asp()
		self.__read_traditional_asp()
		self.toa_index_goal = self.toa_pre_asp_split.index("%% Goal")+1
		self.toa_index_conditions = self.toa_pre_asp_split.index("%% Initial Conditions")+2
		#self.toa_index_new_activity = self.toa_pre_asp_split.index("%% Needs New Activity?")+3
		self.toa_index_activities = self.toa_pre_asp_split.index("%% Existing Activities")+3
		self.traditional_index_goal = self.traditional_pre_asp_split.index("%% Goal")+1
		self.traditional_index_conditions = self.traditional_pre_asp_split.index("%% Initial Conditions")+2


	def __set_activities_list(self):
		reader = open(self.activities_file, 'r')
		activities_text = reader.read()
		reader.close()
		self.activities_list = activities_text.strip().split('\n\n')   # spliting string them in activities
		if(self.activities_list != ['']):
			self.activities_list = [a.split('\n') for a in self.activities_list] # spliting each activity in lines
			if(self.activities_list[-1][-1] == ''): self.activities_list[-1] = self.activities_list[-1][:-1]

	def getActivity(self,initial_conditions,goal):
		start_time = datetime.now()
		self.__writeAsp(initial_conditions,goal)
		activity_name = 0
		new_activity = False
		plan = []
		plan_length = 0
		start_time_first = datetime.now()
		answer = subprocess.check_output('java -jar ' +self.sparcPath + ' ' + self.toa_asp_file +' -A ',shell=True)
		time_first = (datetime.now() - start_time_first).total_seconds()
		time_second = 0
		if(answer == "{}\n"): 
			print("			&&&&&&&&&&&&& Goal already holds &&&&&&&&&&&&&")
			plan = ["Goal Holds"]
			time = (datetime.now() - start_time).total_seconds()
			return [time, time_first, time_second, new_activity,activity_name,plan,plan_length,len(self.activities_list)]
		elif(answer == "\n"):
			print("			############# NEEDS NEW ACTIVITY #############") 
			self.__writeAspNewActivity(initial_conditions,goal)
			start_time_second = datetime.now()
			answer = subprocess.check_output('java -jar ' +self.sparcPath + ' ' + self.new_activity_asp_file +' -A ',shell=True) 
			time_second = (datetime.now() - start_time_second).total_seconds()



			plans = answer.rstrip().split('\n\n') 
    			plans = [plan for plan in plans if plan!='' and plan!='{}']
			chosenPlan = plans[0]
			if chosenPlan == '': 
				print("!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!! UNABLE TO FIND ACTIVITY !!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!")
			plan_in_actions = chosenPlan.strip('}').strip('{').split(', ')
			splitActionsList = [action[:-1].split('),') for action in plan_in_actions]
			splitActionsList.sort(key=lambda x:int(x[1])) 
 			plan_in_actions = ['),'.join(action)+ ')' for action in splitActionsList]
			plan = [ a[7:a.find('),')+1] for a in plan_in_actions]
			
			recorded_activity, activity_name, plan_length = self.__updateActivitiesList(plan, goal)
			if(recorded_activity): 
				self.__updateActivitiesFile()
			new_activity = True
		else:
			print("			     REUSED ACTIVITY") 			 
			plans = answer.rstrip().split('\n\n') 
    			plans = [plan for plan in plans if plan!='' and plan!='{}']
			chosenPlan = plans[0]
			plan_in_actions = chosenPlan.strip('}').strip('{').split(', ')
			splitActionsList = [action[:-1].split('),') for action in plan_in_actions if action[:23] != 'occurs(select_activity(']
			splitActionsList.sort(key=lambda x:int(x[1])) 
 			plan_in_actions = ['),'.join(action)+ ')' for action in splitActionsList]
			plan = [ a[7:a.find('),')+1] for a in plan_in_actions]
			plan_length = len(plan)
			activity_name = int(((chosenPlan[24:]).split(')'))[0])
			#plan = self.activities_list[activity_name-1]

		finish_time = datetime.now()
		time = (finish_time - start_time).total_seconds()
		return [time, time_first, time_second, new_activity,activity_name,plan, plan_length, len(self.activities_list)]

	def __read_toA_asp(self):
		reader = open(self.toa_pre_asp_file, 'r')
		toa_pre_asp = reader.read()
		reader.close()
		self.toa_pre_asp_split = toa_pre_asp.split('\n')

	def __read_traditional_asp(self):
		reader = open(self.traditional_pre_asp_file, 'r')
		traditional_pre_asp = reader.read()
		reader.close()
		self.traditional_pre_asp_split = traditional_pre_asp.split('\n')




	def __writeAsp(self,initial_conditions,goal):
		new_asp = list(self.toa_pre_asp_split)
		if(self.activities_list==['']): max_name = 1
		else: 	max_name =  len(self.activities_list)+1
		new_asp[0] = "#const max_name = " + str(max_name) + "."

		new_asp.insert(self.toa_index_goal,  "selected_goal("+goal+").")
		new_asp.insert(self.toa_index_conditions,initial_conditions)

		activities_strings = ['\n'.join(activity) for activity in self.activities_list]
		final_string = '\n\n'.join(activities_strings)
		new_asp.insert(self.toa_index_activities,final_string)

		asp = '\n'.join(new_asp)
	        f1 = open(self.toa_asp_file, 'w')
		f1.write(asp) 
		f1.close()


	def __writeAspNewActivity(self,initial_conditions,goal):
		new_asp_split = list(self.traditional_pre_asp_split)
		new_asp_split.insert(self.traditional_index_goal,"goal(I) :- holds("+goal+",I).")
		new_asp_split.insert(self.traditional_index_conditions,initial_conditions)
		asp = '\n'.join(new_asp_split)
	        f1 = open(self.new_activity_asp_file, 'w')
		f1.write(asp) 
		f1.close()



	def __updateActivitiesList(self,plan,goal):
		activity_length = len(plan)
		if(activity_length not in [11] or len(self.activities_list) == 20): return False, 0, activity_length
		#if(activity_length not in [11]): return False, 0, activity_length
		activity_name = str(len(self.activities_list)+1)
		new_activity = ['activity_goal('+activity_name+','+goal+').']
		component = 0
		for s in plan:
			component += 1
			new_activity.append('activity_component('+activity_name+','+str(component)+','+s+').')

		if(self.activities_list == []): self.activities_list = [new_activity] 
		else: self.activities_list.append(new_activity)
		return True, activity_name , activity_length


	def __updateActivitiesFile(self):
		activities_strings = ['\n'.join(activity) for activity in self.activities_list]
		final_string = '\n\n'.join(activities_strings)
		writer = open(self.activities_file, 'w')
		writer.write(final_string)
		writer.close()



