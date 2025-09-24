# Emily Miller
# C964 - Computer Science Capstone
# Student ID: 012260948

# Gateway Parcel Co. St. Louis Routing Application
# This program is the application component of my WGU Computer Science Capstone.
# It optimizes local package deliveries for two trucks in St. Louis, Missouri.
# Packages and distances are loaded from CSV files and stored in a custom hash
# table for fast lookups. A greedy nearest-neighbor algorithm with a 2-opt
# refinement step builds efficient delivery routes. The program simulates
# deliveries and provides an interactive console interface to view
# package statuses and total mileage at any time.

import csv
from datetime import datetime, timedelta
from collections import defaultdict
import matplotlib.pyplot as plt
from math import cos, sin, pi

# Define a class for Package
class Package:
    def __init__(self, package_id, address, city, state, zip_code, deadline, weight, notes):
        self.package_id = int(package_id) # I convert package_id to an integer for easier comparisons.
        self.address = address
        self.city = city
        self.state = state
        self.zip_code = zip_code
        self.deadline = deadline  # Deadline is stored as a string (e.g., "10:30 AM")
        self.weight = int(weight)  # I also convert weight to an integer.
        self.notes = notes if notes else ""  # If there are no notes, I store an empty string.
        self.status = "At the hub"  # Initially, every package is at the hub.
        self.delivery_time = None  # This will be updated when the package is delivered.
        self.delayed_delivery = False  # This flag is set if the package has a delayed requirement.
        self.priority = 0  # Priority can be adjusted later based on notes.
        self.truck_assigned = None  # This field stores which truck the package is assigned to.
        self.group_id = None # Used to group packages that must be delivered together.
        self.related_ids = None # Only one package in group seems to dictate what others are in the group, so it will keep track here for handling grouping logic
        self.forced_truck = None # Added to handle special note for packages that must be on truck 2
        self.hold = False # Used for special case for package 9 where package will not get assigned till after the address is updated
        self.original_address = None
        self.address_update_time = None

# Define a class for Truck
class Truck:
    def __init__(self, capacity=16):  # Each truck can carry up to 16 packages per trip.
        self.capacity = capacity
        self.packages = []  # This list will store the packages for the current trip.
        self.total_distance = 0.0  # This will accumulate the total distance traveled over all trips.
        self.current_time = datetime.strptime("08:00 AM", "%I:%M %p") # I set the truck's clock to start at 8:00 AM (the earliest departure time).
        self.at_hub = True  # Initially, the truck is at the hub.
        self.current_location = "4001 S 700 E"  # This is the hub address.
        self.trip_history = []  # A list to record the state of each trip.
        self.routes = [] #list of dicts per trip
        self.baseline_distance = 0.0

# Define a hash table class for storing packages
class HashTable:
    def __init__(self, size):
        self.size = size
        # I initialize the table with a list of None values.
        self.table = [None] * size

    def _hash(self, key):
        # I use the modulo operator to compute the hash index.
        return key % self.size

    def insert(self, key, value):
        index = self._hash(key)
        # If the slot is empty, I create a new list.
        if not self.table[index]:
            self.table[index] = []
        self.table[index].append(value)  # I append the package object.

    def search(self, key):
        index = self._hash(key)
        # I search the list at the computed index for the package with the matching ID.
        if self.table[index]:
            for package in self.table[index]:
                if package.package_id == key:
                    return package
        return None

# Computes a weighted score for the package based on its deadline and its special priority. Lower scores indicate that the package should be prioritized.
def priority_score(pkg):
    base_time = datetime.strptime("08:00 AM", "%I:%M %p")
    if pkg.deadline.strip().upper() == "EOD":
        deadline_dt = datetime.strptime("05:00 PM", "%I:%M %p") # Treat end of day as 5PM
    else:
        deadline_dt = datetime.strptime(pkg.deadline.strip(), "%I:%M %p")
    # Compute difference in minutes from 8:00 AM.
    diff_minutes = (deadline_dt - base_time).total_seconds() / 60
    # Let the weight factor be 30 minutes per priority point.
    weight_factor = 30
    score = diff_minutes - (weight_factor * pkg.priority)
    return score

# Function to load package data from CSV
def load_package_data(filename):
    # I create a hash table to store packages for fast lookup.
    package_hash = HashTable(50)
    # I use a defaultdict to track groups of packages that must be delivered together.
    grouped_packages = defaultdict(list)

    with open(filename, 'r') as file:
        reader = csv.reader(file)
        next(reader)  # I skip the header row.

        for row in reader:
            # I create a Package object for each row in the CSV.
            package = Package(
                row[0],
                clean_address(row[1]),  # I clean the address string.
                row[2],
                row[3],
                row[4],
                row[5],
                row[6],
                row[7]
            )

            # Set package 9 to hold until it's address can be updated and save the original incorrect address
            if package.package_id == 9:
                package.hold = True
                package.original_address = package.address

            # If the note indicates that the package can only be on Truck 2, set forced_truck accordingly
            if "Can only be on truck 2" in row[7]:
                package.forced_truck = 2

            # Based on special notes, set package priorities and group packages.
            if "Must be delivered with" in row[7]:
                # Remove commas so that numbers like "15," become "15"
                note_clean = row[7].replace(',', '')
                # Parse all digits from the cleaned note.
                package.related_ids = [int(s) for s in note_clean.split() if s.isdigit()]
                # Use the largest id from the grouped packages as the group id since this will loop over all packages smallest to largest
                if package.related_ids:
                    package.group_id = max([package.package_id] + package.related_ids)
                else:
                    package.group_id = package.package_id
                package.priority = 2  # Higher priority for grouped packages.
            elif "Delayed" in row[7]:
                package.priority = 1
                package.delayed_delivery = True
            elif "EOD" not in row[5]:
                package.priority = 1
            else:
                package.priority = 0

            package_hash.insert(package.package_id, package)

    # Handle grouping logic for packages that are grouped but don't have a note mentioning their grouping
    all_packages = [package_hash.search(i) for i in range(1, 41)]
    for pkg in all_packages:
        # Check if the package has any related_ids.
        if pkg.related_ids is not None:
            # Save the original package's group_id.
            group_id = pkg.group_id
            
            # Start with the original package's forced_truck value.
            forced_truck_value = pkg.forced_truck

            # Loop over each related package id.
            for related_id in pkg.related_ids:
                # Use search method to get the related package.
                related_pkg = package_hash.search(related_id)
                if related_pkg is not None:
                    # Set the related package's group_id to match the original package.
                    related_pkg.group_id = group_id
                    related_pkg.priority = 2  # Higher priority for grouped packages.
                    
                    # If this related package has a forced_truck value, capture it.
                    if related_pkg.forced_truck is not None:
                        forced_truck_value = related_pkg.forced_truck

            # If any package in related_ids (or the original package) had forced_truck set,
            # update the forced_truck property on both the original package and all related packages.
            if forced_truck_value is not None:
                pkg.forced_truck = forced_truck_value
                for related_id in pkg.related_ids:
                    related_pkg = package_hash.search(related_id)
                    if related_pkg is not None:
                        related_pkg.forced_truck = forced_truck_value

    return package_hash

# Function to load distance and address data from CSV
def load_distance_data(filename):
    distances = []
    addresses = []

    with open(filename, 'r') as file:
        reader = csv.reader(file)
        headers = next(reader)
        # I assume the first two columns are not addresses; the rest are.
        addresses = [clean_address(header) for header in headers[2:]]
        hub = "4001 S 700 E"
        # I verify that the hub address is in the list of addresses.
        if hub not in addresses:
            print("Actual cleaned addresses in distance table:")
            for idx, addr in enumerate(addresses):
                print(f"{idx}: {addr}")
            raise ValueError(f"Hub address '{hub}' not found in distance table")
        # I load the distance values, converting them to floats.
        for row in reader:
            row_distances = []
            for cell in row[2:]:
                if cell.strip():
                    try:
                        row_distances.append(float(cell.strip()))
                    except ValueError:
                        row_distances.append(0.0)
                else:
                    row_distances.append(0.0)
            distances.append(row_distances)
    
    return distances, addresses

# Function to clean an address string
def clean_address(raw_address):
    # I check for the hub address first.
    if "4001 South 700 East" in raw_address:
        return "4001 S 700 E"
    # I handle a special case for package #9.
    if "300 State St" in raw_address:
        return "300 STATE ST"
    # I extract the actual address by splitting the string.
    address = raw_address.split('\n')[-1].split(',')[0].strip()
    # I use a dictionary to replace full words with abbreviations.
    replacements = {
        'South': 'S', 'North': 'N', 'East': 'E', 'West': 'W',
        'Street': 'ST', 'Avenue': 'AVE', 'Blvd': 'BLVD', 'Rd': 'RD'
    }
    for full, abbrev in replacements.items():
        address = address.replace(full, abbrev)
    return address.upper()

# Function to calculate distance between two addresses using the triangular matrix
def distance_between(address1, address2, addresses, distances):
    try:
        index1 = addresses.index(address1)
        index2 = addresses.index(address2)
    except ValueError as e:
        # I print a helpful error message if an address lookup fails.
        print(f"Address lookup failed: {e}")
        print(f"Address1: {address1}")
        print(f"Address2: {address2}")
        print("Available addresses:")
        for i, addr in enumerate(addresses):
            print(f"{i}: {addr}")
        raise
    # I use the lower triangle of the matrix.
    i = min(index1, index2)
    j = max(index1, index2)
    return distances[j][i]

# Function to find the nearest address using a greedy approach
def min_distance_from(current_address, unvisited_addresses, addresses, distances):
    if not unvisited_addresses:
        return None
    nearest_address = None
    shortest_distance = float('inf')
    # I iterate over all unvisited addresses and pick the one with the smallest distance.
    for address in unvisited_addresses:
        if address not in addresses:
            print(f"Warning: Address {address} not found in address list")
            continue
        dist = distance_between(current_address, address, addresses, distances)
        if dist < shortest_distance:
            shortest_distance = dist
            nearest_address = address
    return nearest_address

# Gets status of a specific package at a specific time
def get_status_at(pkg, query_time):
    base_start = datetime.strptime("8:00 AM", "%I:%M %p")
    # If the package has been delivered and the delivery time is less than or equal to query_time:
    if pkg.delivery_time and pkg.delivery_time <= query_time:
        return f"Delivered at {pkg.delivery_time.strftime('%I:%M %p')} (Truck {pkg.truck_assigned})"
    elif query_time <= base_start:
        return "At the hub"
    # If the package has been assigned to a truck but its recorded delivery time is in the future:
    elif pkg.truck_assigned:
        return f"En route (Truck {pkg.truck_assigned})"
    else:
        return "At the hub"
    
def get_display_address(pkg, query_time):
    if pkg.package_id == 9 and pkg.address_update_time is not None and query_time < pkg.address_update_time:
        return pkg.original_address
    return pkg.address

# Function to display the status of all packages.
# If no query time is given, I use the current system time.
def display_package_status(package_hash, query_time=None):
    if query_time is None:
        query_time = datetime.now()
    for package_id in range(1, 41):
        pkg = package_hash.search(package_id)
        status = get_status_at(pkg, query_time)
        print(f"Package ID: {pkg.package_id}          Delivery Status: {status}          Delivery Deadline: {pkg.deadline}          Delivery Address: {pkg.address}          Truck Number: {pkg.truck_assigned}")

# Function to display the total mileage traveled by all trucks.
def display_total_mileage(trucks):
    total_mileage = sum(truck.total_distance for truck in trucks)
    print(f"\nTotal mileage traveled by all trucks: {total_mileage:.2f} miles")

# 2-opt optimization functions for route improvement below. Previously was exceeding 140 mile limit with my original implementation of nearest neighbors.

# This function computes the total distance of a given route.
def route_distance(route, addresses, distances):
    total = 0
    for i in range(len(route) - 1):
        total += distance_between(route[i], route[i+1], addresses, distances)
    return total

# The two_opt function tries to improve the route by reversing segments.
def two_opt(route, addresses, distances):
    best_route = route
    best_distance = route_distance(best_route, addresses, distances)
    improved = True
    # I keep trying to improve the route until no further improvement is found.
    while improved:
        improved = False
        for i in range(1, len(best_route) - 2):
            for j in range(i+1, len(best_route) - 1):
                new_route = best_route[:i] + best_route[i:j+1][::-1] + best_route[j+1:]
                new_distance = route_distance(new_route, addresses, distances)
                if new_distance < best_distance:
                    best_route = new_route
                    best_distance = new_distance
                    improved = True
        route = best_route
    return best_route

# Functions for planning and delivering a single trip for a truck below.

# This function plans an initial route for a truck using a greedy nearest neighbor approach.
def plan_truck_route(truck, addresses, distances):
    hub = "4001 S 700 E"
    current_address = hub
    # I use a set (converted to list) of unique cleaned addresses from the truck's packages.
    unvisited = list({clean_address(pkg.address) for pkg in truck.packages})
    route = [hub]
    # I keep adding the nearest unvisited address until all have been visited.
    while unvisited:
        next_address = min_distance_from(current_address, unvisited, addresses, distances)
        route.append(next_address)
        unvisited.remove(next_address)
        current_address = next_address
    route.append(hub)  # End the route at the hub.
    return route

# This function simulates the delivery for a truck on one trip along a planned route.
def deliver_truck_route(truck, route, addresses, distances):
    hub = "4001 S 700 E"
    # I do not reset truck.current_time because I want time to accumulate over trips.
    for i in range(len(route) - 1):
        leg_distance = distance_between(route[i], route[i+1], addresses, distances)
        truck.total_distance += leg_distance  # I add the distance of each leg to the truck's total.
        travel_time = leg_distance / 18  # I calculate travel time assuming a speed of 18 mph.
        truck.current_time += timedelta(hours=travel_time)
        if route[i+1] != hub:
            # For each package with a matching address, I mark it as delivered.
            for pkg in truck.packages[:]:
                if clean_address(pkg.address) == route[i+1]:
                    pkg.delivery_time = truck.current_time
                    pkg.status = f"Delivered at {pkg.delivery_time.strftime('%I:%M %p')} (Truck {pkg.truck_assigned})"
                    truck.packages.remove(pkg)
    truck.at_hub = True

# Multi-trip simulation function to deliver all packages while respecting truck capacity.
def simulate_deliveries(trucks, addresses, distances, package_hash):
    # I gather all packages (IDs 1 to 40) into a list.
    all_packages = [package_hash.search(i) for i in range(1, 41)]
    # I define undelivered packages as those that have no delivery_time set.
    undelivered = [pkg for pkg in all_packages if pkg.delivery_time is None]
    # I continue simulation until every package has been delivered.
    while undelivered:
        sorted_packages = sorted(undelivered, key=priority_score)
        # Record the current trip for each truck.
        for truck in trucks:
            truck.packages = []
        # Separate grouped and individual packages.
        group_dict = {}
        individuals = []
        for pkg in sorted_packages:
            if pkg.group_id is not None:
                group_dict.setdefault(pkg.group_id, []).append(pkg)
            else:
                individuals.append(pkg)
        # Assign grouped packages first.
        for group in group_dict.values():
            # Try to assign the entire group to a truck.
            forced_truck_for_group = None
            for p in group:
                if p.forced_truck is not None:
                    forced_truck_for_group = p.forced_truck
                    break
            if forced_truck_for_group is not None:
                target_truck = trucks[forced_truck_for_group - 1]
                if len(target_truck.packages) + len(group) <= target_truck.capacity:
                    for p in group:
                        target_truck.packages.append(p)
                        p.truck_assigned = forced_truck_for_group
            else:
                for truck in trucks:
                    if len(truck.packages) + len(group) <= truck.capacity:
                        for p in group:
                            truck.packages.append(p)
                            p.truck_assigned = trucks.index(truck) + 1
                        break
            # If the entire group cannot be assigned in this cycle, do nothing.
            # They will be reattempted in a later simulation cycle.

        # Assign individual packages.
        for pkg in individuals:            
            for truck in trucks:
                # For package #9, only assign if the truck's current time is >= 10:20 AM.
                if pkg.package_id == 9:
                    if truck.current_time < datetime.strptime("10:20 AM", "%I:%M %p"):
                        # Skip this truck for package #9; it remains unassigned this cycle.
                        continue
                    else:
                        # Update package #9's address when eligible.
                        pkg.address_update_time = truck.current_time
                        pkg.address = "410 S STATE ST"
                        pkg.hold = False
                        pkg.forced_truck = trucks.index(truck) + 1
                elif pkg.delayed_delivery:
                    if truck.current_time < datetime.strptime("9:05 AM", "%I:%M %p"):
                        # Skip this truck for the package; it remains unassigned this cycle.
                        continue
                    else:
                        # Truck 2 is setup to wait for the delayed flight - make sure packages that are on the delayed flight are forced to this truck
                        pkg.forced_truck = 2
                        # Update the package to un-delay it
                        pkg.delayed_delivery = False


            # Check handling skipping package #9 if necessary, as well as the delayed packages
            if pkg.hold or pkg.delayed_delivery:
                continue
            else:
                # If this package is forced to a specific truck, assign it only to that truck.
                if pkg.forced_truck is not None:
                    target_truck = trucks[pkg.forced_truck - 1]
                    if len(target_truck.packages) < target_truck.capacity:
                        target_truck.packages.append(pkg)
                        pkg.truck_assigned = pkg.forced_truck
                        continue
                    else:
                        continue  # Leave unassigned if forced truck is full.
                else:
                    # Regular assignment to the first truck with available capacity.
                    for truck in trucks:
                        if len(truck.packages) < truck.capacity:
                            truck.packages.append(pkg)
                            pkg.truck_assigned = trucks.index(truck) + 1
                            break
        # Record trip history before delivering.
        for truck in trucks:
            if truck.packages:
                # Save the load and start time.
                trip_start_load = truck.packages.copy()
                trip_start_time = truck.current_time
                initial_route = plan_truck_route(truck, addresses, distances)
                baseline_miles = route_distance(initial_route, addresses, distances)
                truck.baseline_distance += baseline_miles
                optimized_route = two_opt(initial_route, addresses, distances)
                #record the initial and optimized routes
                truck.routes.append({
                    "initial_route": initial_route[:],
                    "optimized_route": optimized_route[:]
                })
                #accumulate baseline distance (distance before 2-opt)
                deliver_truck_route(truck, optimized_route, addresses, distances)
                # Append a trip record to trip_history.
                truck.trip_history.append({
                    "start_time": trip_start_time,
                    "end_time": truck.current_time,
                    "packages": trip_start_load
                })
        undelivered = [pkg for pkg in all_packages if pkg.delivery_time is None]

# Function to display truck loads (which packages are loaded on each truck) at a given query time.
def display_truck_loads(trucks, query_time):
    print(f"\nTruck Loads at {query_time.strftime('%I:%M %p')}:")
    for idx, truck in enumerate(trucks):
        # Look for a trip in the truck's history that covers the query time.
        found = False
        for trip in truck.trip_history:
            if trip["start_time"] <= query_time <= trip["end_time"]:
                print(f"Truck {idx+1}:")
                for pkg in trip["packages"]:
                    # For display, compute virtual status.
                    status = get_status_at(pkg, query_time)
                    print(f"Package ID: {pkg.package_id}          Status: {status}          Delivery Deadline: {pkg.deadline}          Delivery Address: {pkg.address}          Truck Number: {pkg.truck_assigned}")
                found = True
                break
        if not found:
            # If no historical trip covers the query time, check if a trip is in progress.
            if truck.packages and truck.current_time > query_time:
                print(f"Truck {idx+1} (current load):")
                for pkg in truck.packages:
                    status = get_status_at(pkg, query_time)
                    print(f"Package ID: {pkg.package_id}          Status: {status}          Delivery Deadline: {pkg.deadline}          Delivery Address: {pkg.address}          Truck Number: {pkg.truck_assigned}")
            else:
                print(f"Truck {idx+1}: (No trip active at this time)")

# Interactive menu for the supervisor to view statuses and mileage.
def main_menu(package_hash, trucks):
    while True:
        print("\nMain Menu")
        print("1. View the status of all packages")
        print("2. Query the status of a single package at a specific time")
        print("3. Query the status of all packages at a specific time")
        print("4. View total mileage traveled by all trucks")
        print("5. View truck loads at a specific time")
        print("6. Exit")
        choice = input("Enter your choice: ")

        if choice == "1":
            display_package_status(package_hash)
        elif choice == "2":
            try:
                query_time = input("Enter a time (HH:MM AM/PM): ")
                query_time = datetime.strptime(query_time, "%I:%M %p")
                package_id = int(input("Enter the package ID: "))
                package = package_hash.search(package_id)
                if package:
                    status = get_status_at(package, query_time)
                    display_address = get_display_address(package, query_time)
                    print(f"Package ID: {package.package_id}          Delivery Status: {status}          Delivery Deadline: {package.deadline}          Delivery Address: {display_address}          Truck Number: {package.truck_assigned}")
                else:
                    print("Package not found.")
            except ValueError:
                print("Invalid input. Please try again.")
        elif choice == "3":
            try:
                query_time = input("Enter a time (HH:MM AM/PM): ")
                query_time = datetime.strptime(query_time, "%I:%M %p")
                print(f"\nPackage Status at {query_time.strftime('%I:%M %p')}:")
                for package_id in range(1, 41):
                    package = package_hash.search(package_id)
                    status = get_status_at(package, query_time)
                    display_address = get_display_address(package,query_time)
                    print(f"Package ID: {package.package_id}          Delivery Status: {status}          Delivery Deadline: {package.deadline}          Delivery Address: {display_address}          Truck Number: {package.truck_assigned}")
            except ValueError:
                print("Invalid time format")
        elif choice == "4":
            display_total_mileage(trucks)
        elif choice == "5":
            try:
                query_time = input("Enter a time (HH:MM AM/PM): ")
                query_time = datetime.strptime(query_time, "%I:%M %p")
                display_truck_loads(trucks, query_time)
            except ValueError:
                print("Invalid time format")
        elif choice == "6":
            print("Exiting program.")
            break
        else:
            print("Invalid choice. Please try again.")

# Creates and saves three visuals for Part C/D of the capstone.
# Each visualization is saved as a PNG file and closed after saving so figures don't overlap or block execution.
def generate_visualizations(package_hash, trucks, addresses, distances):

    try:
        # Histogram of delivery times (minutes since 8:00 AM)
        plot_delivery_time_histogram(package_hash)
        plt.savefig("delivery_times_hist.png", bbox_inches="tight")
        print("Saved: delivery_times_hist.png")
        plt.close()
    except Exception as e:
        print(f"Could not generate delivery time histogram: {e}")

    try:
        # Bar chart comparing baseline vs. optimized total mileage
        plot_mileage_comparison(trucks)
        plt.savefig("mileage_comparison.png", bbox_inches="tight")
        print("Saved: mileage_comparison.png") 
        plt.close()
    except Exception as e:
        print(f"Could not generate mileage comparison: {e}")

    try:
        # Bar chart showing miles traveled by each truck
        plot_miles_per_truck(trucks)
        plt.savefig("miles_per_truck.png", bbox_inches="tight")
        print("Saved: miles_per_truck.png")
        plt.close()
    except Exception as e:
        print(f"Could not generate route diagram: {e}")

#Create a histogram of package delivery times (minutes after 8:00 AM).
# Uses the delivery_time attribute recorded for each package.
def plot_delivery_time_histogram(package_hash):
    base = datetime.strptime("8:00 AM", "%I:%M %p")
    mins_since_base = []

    #collect delivery times (hour of day)
    for pkg_id in range(1,41):
        pkg = package_hash.search(pkg_id)
        if pkg and getattr(pkg, "delivery_time", None):
            delta_min = (pkg.delivery_time - base).total_seconds() / 60.0
            if delta_min >= 0:
                mins_since_base.append(delta_min)
    
    plt.figure()
    plt.hist(mins_since_base, bins=10)
    plt.title("Distribution of Delivery Times (minutes since 8:00 AM)")
    plt.xlabel("Minutes since 8:00 AM")
    plt.ylabel("Package count")

# Compares baseline mileage (pre-optimization) with optimized mileage (post 2-opt).
# Baseline values must be recorded earlier in the simulation
def plot_mileage_comparison(trucks):
    baseline_total = sum(getattr(t, "baseline_distance", 0.0) for t in trucks)    
    optimized_total = sum(getattr(t, "total_distance", 0.0) for t in trucks)

    plt.figure()
    labels = ["Baseline", "Optimized"]
    values = [baseline_total, optimized_total]
    plt.bar(labels, values)
    plt.title("Total Mileage: Baseline vs Optimized")
    plt.ylabel("Miles")

# Shows mileage per truck to illustrate workload distribution.
def plot_miles_per_truck(trucks):
    plt.figure()
    labels= [f"Truck {i+1}" for i in range(len(trucks))]
    values = [getattr(t, "total_distance", 0.0) for t in trucks]
    plt.bar(labels, values)
    plt.title("Miles per Truck")
    plt.ylabel("Miles")




# Main function where the simulation and user interface are initiated.
def main():
    # I load package data from the WGUPS package CSV file.
    package_hash = load_package_data("./WGUPS_Package_File.csv")
    # I load distance and address data from the WGUPS distance table CSV file.
    distances, addresses = load_distance_data("./WGUPS_Distance_Table.csv")

    # I create two Truck objects.
    trucks = [Truck() for _ in range(2)]

    # Start truck 2 at 9:05 AM so it can "wait" on the delayed packages
    trucks[1].current_time = datetime.strptime("9:05 AM", "%I:%M %p")

    # I simulate the delivery process, ensuring each truck carries at most 16 packages per trip.
    simulate_deliveries(trucks, addresses, distances, package_hash)

    # After simulation, I display the total mileage and launch the interactive menu for further queries.
    display_total_mileage(trucks)

    actual_total = sum(t.total_distance for t in trucks)
    baseline_total = sum(t.baseline_distance for t in trucks)

    if baseline_total > 0:
        improvement = (baseline_total - actual_total) / baseline_total * 100.0
        print(f"Baseline (pre-optimization) miles: {baseline_total:.2f}")
        print(f"Optimized total miles:           {actual_total:.2f}")
        print(f"Improvement:                     {improvement:.1f}%")
    else:
        print("Baseline miles not available (no initial routes recorded).")

    generate_visualizations(package_hash, trucks, addresses, distances)
    main_menu(package_hash, trucks)

# Entry point of the program.
if __name__ == "__main__":
    main()