#lang forge

option local_necessity on 
sig NetworkUser {
    follows: set NetworkUser,
    isVerified: one Bool,
    hasProfilePic: one Bool
}

abstract sig Bool {} 
one sig Yes extends Bool {}
one sig No extends Bool {}
one sig NetworkOwner extends NetworkUser {}

-- Properties that hold: 
-- (1) weHang users (excluding the NetworkOwner) can follow nobody
-- (2) The NetworkOwner needs to follow all weHang users  
-- (3) weHang users can't follow themselves
-- (4) weHang users (excluding the NetworkOwner) are verified if they have more than 2 followers
--     and have a profile pic
-- (5) The NetworkOwner is always verified
-- (6) The NetworkOwner needs to have a profile picture 

-- Properties that don't hold:
-- (1) follows is a symmetric relation
-- (2) not all users can be verified 
-- (4) weHang users can have no followers

pred noSelfFollower {
    no iden & follows
}

pred verifiedNetworkUser {
    all w:NetworkUser - NetworkOwner | ((#(follows.w) > 2) and w.hasProfilePic = Yes) iff w.isVerified = Yes
}

pred NetworkOwnerRestriction {
    no follows.NetworkOwner
    NetworkOwner.isVerified = Yes
    NetworkOwner.hasProfilePic = Yes 
}

pred NetworkOwnerFollowsAll {
    all w:NetworkUser - NetworkOwner | w in NetworkOwner.follows
}

pred weHangSimulation {
    noSelfFollower
    verifiedNetworkUser
    NetworkOwnerFollowsAll
    NetworkOwnerRestriction
}

example tryingBreakingInstance is not weHangSimulation for {
    NetworkOwner = NetworkOwner0
    NetworkUser = NetworkUser0 + NetworkUser1 + NetworkUser2 + NetworkOwner0
    No = No0
    Yes = Yes0
    follows = NetworkOwner0->NetworkUser0 + NetworkOwner0->NetworkUser1 + NetworkOwner0->NetworkUser2 +
              NetworkUser0->NetworkUser2 + NetworkUser2->NetworkUser0 + NetworkUser2->NetworkUser1
    isVerified = NetworkOwner0->Yes + NetworkUser0->Yes + NetworkUser1->No + NetworkUser2->No
    hasProfilePic = NetworkOwner0->Yes + NetworkUser0->Yes + NetworkUser1->Yes + NetworkUser2->No
}

example tryingBreakingInstance2 is  weHangSimulation for {
    NetworkOwner = NetworkOwner0
    NetworkUser = NetworkUser0 + NetworkUser1 + NetworkUser2 + NetworkOwner0
    No = No0
    Yes = Yes0
    follows = NetworkOwner0->NetworkUser0 + NetworkOwner0->NetworkUser1 + NetworkOwner0->NetworkUser2 + NetworkUser0->NetworkUser2 + NetworkUser2->NetworkUser0 + NetworkUser2->NetworkUser1 + NetworkUser1->NetworkUser0
    isVerified = NetworkOwner0->Yes + NetworkUser0->Yes + NetworkUser1->No + NetworkUser2->No
    hasProfilePic = NetworkOwner0->Yes + NetworkUser0->Yes + NetworkUser1->Yes + NetworkUser2->No
}


-- ~instance 6 or so for Tim on PC
test expect {
    shouldBeUnsat: {weHangSimulation} for {
      NetworkOwner = NetworkOwner0
      NetworkUser = NetworkUser0 + NetworkUser1 + NetworkUser2 + NetworkOwner0
      No = No0
      Yes = Yes0
      follows = NetworkOwner0->NetworkUser0 + NetworkOwner0->NetworkUser1 + NetworkOwner0->NetworkUser2 +
                NetworkUser0->NetworkUser2 + NetworkUser2->NetworkUser0 + NetworkUser2->NetworkUser1
                -- removed NetworkUSer1->NetworkUser0
      isVerified = NetworkOwner0->Yes + NetworkUser0->Yes + NetworkUser1->No + NetworkUser2->Yes
      hasProfilePic = NetworkOwner0->Yes + NetworkUser0->Yes + NetworkUser1->No + NetworkUser2->Yes
    } is unsat
}


option verbose 2
run weHangSimulation for exactly 4 NetworkUser, 4 Int

