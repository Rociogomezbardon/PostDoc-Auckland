# -*- coding: utf-8 -*-
'''
'''

all_activities_file = 'all_activities.txt'
selected_activities_file = 'selected_activities.txt'
activities_list = []
chosen_activity_lengths = [13]
if __name__ == "__main__":
	reader = open(all_activities_file, 'r')
	activities_text = reader.read()
	reader.close()
	activities_list = activities_text.strip().split('\n\n')   # spliting string them in activities
	activities_list = [a.split('\n') for a in activities_list] # spliting each activity in lines
	if(activities_list[-1][-1] == ''): activities_list[-1] = activities_list[-1][:-1]
	selected_activities_list = [a for a in activities_list if len(a)-1 in chosen_activity_lengths]
	count = 0
	selected_activities_list = [[line[:line.find('(')+1] + str(selected_activities_list.index(a)+1) + line[line.find(','):] for line in a] for a in selected_activities_list]
		
		
	selected_activities_strings = ['\n'.join(activity) for activity in selected_activities_list]
	final_string = '\n\n'.join(selected_activities_strings)
	writer = open(selected_activities_file, 'w')
	writer.write(final_string)
	writer.close()


	
